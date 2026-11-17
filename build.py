# release build
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import signal
import subprocess
import sys
import tarfile
import time


TARGETS = (
    ('campaign', 'solver/build.py', ()),
    ('state-verification', 'reconstruction/build_states.py', ()),
    ('placement-verification', 'reconstruction/build_placements.py', ('--variant', 'placements')),
)


def digest(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        while block := stream.read(1024 * 1024):
            value.update(block)
    return value.hexdigest()


def package_file(package, name):
    relative = PurePosixPath(name)
    if relative.is_absolute() or '..' in relative.parts:
        raise ValueError('invalid package path: ' + name)
    path = (package / name).resolve(strict=True)
    if package not in path.parents or not path.is_file():
        raise ValueError('file outside package: ' + name)
    return path


def extract_source(archive_path, destination, source_name):
    with tarfile.open(archive_path, 'r:gz') as archive:
        members = archive.getmembers()
        seen = set()
        for member in members:
            path = PurePosixPath(member.name)
            if path.is_absolute() or '..' in path.parts or not path.parts or \
                    path.parts[0] != source_name or not (member.isfile() or member.isdir()) or path in seen:
                raise ValueError('invalid dependency archive member: ' + member.name)
            seen.add(path)
        archive.extractall(destination, members=members)
    source = destination / source_name
    if not (source / 'configure').is_file():
        raise ValueError('dependency configure script missing')
    return source


def interrupt(signum, frame):
    raise KeyboardInterrupt


def run_step(name, command, directory, output, environment, steps):
    stdout_path, stderr_path = output / (name + '.out'), output / (name + '.err')
    started = time.monotonic()
    process = None
    with stdout_path.open('xb') as stdout, stderr_path.open('xb') as stderr:
        try:
            process = subprocess.Popen(command, cwd=directory, stdout=stdout, stderr=stderr,
                                       env=environment, start_new_session=True)
            returncode = process.wait()
        except BaseException:
            if process is not None:
                try:
                    os.killpg(process.pid, signal.SIGTERM)
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    pass
                except ProcessLookupError:
                    pass
                finally:
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    process.wait()
            raise
    steps.append({'name': name, 'command': command, 'directory': str(directory),
                  'exit_code': returncode, 'wall_seconds': time.monotonic() - started,
                  'stdout_sha256': digest(stdout_path), 'stderr_sha256': digest(stderr_path)})
    if returncode:
        raise RuntimeError(name + ' failed; see ' + str(stderr_path))


def main():
    package = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description='Offline build of the solver, reconstruction programs and both checkers.')
    parser.add_argument('--build-directory', type=Path, default=package / 'build',
                        help='new output directory (default: release/build); binaries in each target/bin/')
    parser.add_argument('--jobs', type=int, default=8, help='dependency build workers (default: 8)')
    parser.add_argument('--compiler', help='C++ compiler (default: clang++ or g++)')
    parser.add_argument('--cc', help='C compiler (default: clang or gcc)')
    args = parser.parse_args()
    try:
        if args.jobs <= 0:
            raise ValueError('jobs must be positive')
        if args.build_directory.exists() or args.build_directory.is_symlink():
            raise ValueError('build directory already exists; use a new --build-directory')
        output = args.build_directory.resolve()
        if any(character.isspace() for character in str(output)):
            raise ValueError('nauty requires a path without whitespace; choose --build-directory without spaces')
        manifest_path = package / 'manifest.json'
        manifest = json.loads(manifest_path.read_text())
        recipe, files = manifest['build'], manifest['files']
        if not isinstance(files, dict) or any(not isinstance(name, str) for name in files):
            raise ValueError('files must be an object with package paths')
        dependency = recipe['dependency']
        archive_name, source_name = dependency['archive'], dependency['source_directory']
        if source_name != 'nauty2_9_3':
            raise ValueError('unsupported dependency source directory')
        archive = package_file(package, archive_name)
        inputs = {manifest_path.name: digest(manifest_path)}
        names = {archive_name, 'build.py', 'certificates.json'} | {script for _, script, _ in TARGETS}
        names |= {name for name in files if name.split('/')[0] in ('solver', 'checkers', 'reconstruction') or name == 'trees.txt'}
        for name in sorted(names):
            path = package_file(package, name)
            actual = digest(path)
            if actual != files[name]['sha256']:
                raise ValueError('package SHA-256 differs: ' + name)
            inputs[name] = actual
        compiler = shutil.which(args.compiler) if args.compiler else shutil.which('clang++') or shutil.which('g++')
        cc = shutil.which(args.cc) if args.cc else shutil.which('clang') or shutil.which('gcc')
        make = shutil.which('make')
        if not compiler or not cc or not make:
            raise ValueError('C/C++ compilers and make are required')
        output.mkdir(parents=True, exist_ok=False)
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.error(str(error))
    signal.signal(signal.SIGTERM, interrupt)
    signal.signal(signal.SIGINT, interrupt)
    started = time.monotonic()
    record = {'status': 'building', 'started_at': datetime.now(timezone.utc).isoformat(),
              'inputs_sha256': inputs, 'steps': []}
    environment = dict(os.environ, CC=cc, CXX=compiler)
    try:
        source = extract_source(archive, output / 'dependency-source', source_name)
        prefix = output / 'dependency'
        run_step('configure', ['./configure', '--enable-tls', '--prefix=' + str(prefix),
                              '--includedir=' + str(prefix / 'include/nauty')],
                 source, output, environment, record['steps'])
        run_step('dependency-build', [make, '-j' + str(args.jobs), 'all', 'TLSlibs'],
                 source, output, environment, record['steps'])
        run_step('dependency-install', [make, 'install', 'TLSinstall'],
                 source, output, environment, record['steps'])
        native_manifests = {}
        for target, script_name, arguments in TARGETS:
            target_directory = output / target
            target_directory.mkdir()
            script = package_file(package, script_name)
            run_step(target, [sys.executable, str(script), *arguments,
                              '--output', str(target_directory / 'bin'), '--nauty-prefix', str(prefix),
                              '--compiler', compiler, '--cc', cc],
                     package, output, environment, record['steps'])
            native_manifest = target_directory / 'bin/BUILD.json'
            if json.loads(native_manifest.read_text())['status'] != 'built':
                raise RuntimeError(target + ' build did not complete')
            native_manifests[target] = digest(native_manifest)
        if any(digest(package_file(package, name)) != expected for name, expected in inputs.items()):
            raise RuntimeError('package inputs changed during build')
        record.update(status='built', native_manifest_sha256=native_manifests)
        returncode = 0
    except (Exception, KeyboardInterrupt) as error:
        record.update(status='failed', error=str(error) or type(error).__name__)
        returncode = 130 if isinstance(error, KeyboardInterrupt) else 1
    record.update(finished_at=datetime.now(timezone.utc).isoformat(), wall_seconds=time.monotonic() - started)
    with (output / 'BUILD.json').open('x') as stream:
        json.dump(record, stream, indent=2)
        stream.write('\n')
    print(json.dumps({'status': record['status'], 'build_directory': str(output),
                      'binaries': {target: str(output / target / 'bin') for target, _, _ in TARGETS},
                      'receipt': str(output / 'BUILD.json'),
                      **({'error': record['error']} if 'error' in record else {})}))
    return returncode


if __name__ == '__main__':
    raise SystemExit(main())

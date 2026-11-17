# certificate verification launcher
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import sys


def digest(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        while block := stream.read(1024 * 1024):
            value.update(block)
    return value.hexdigest()


def package_file(root, name):
    relative = PurePosixPath(name)
    if relative.is_absolute() or '..' in relative.parts or not relative.parts or relative.as_posix() != name:
        raise ValueError('invalid package path: ' + name)
    path = root / name
    if any((root / Path(*relative.parts[:index])).is_symlink()
           for index in range(1, len(relative.parts) + 1)):
        raise ValueError('symlink in package path: ' + name)
    resolved = path.resolve(strict=True)
    if root not in resolved.parents or not resolved.is_file():
        raise ValueError('file outside package: ' + name)
    return resolved


def release_file(release, files, name):
    path = package_file(release, name)
    if digest(path) != files[name]['sha256']:
        raise ValueError('release file differs: ' + name)
    return path


def source_hash(path, original_name):
    content = path.read_bytes()
    prefix = b'#' if path.suffix == '.py' else b'//'
    lines = content.splitlines(keepends=True)
    for index, line in enumerate(lines):
        if not line.startswith(prefix):
            break
        lines[index] = line.replace(b' > ', b' -> ')
    content = b''.join(lines)
    if original_name == 'source/parallel-reconstruction/compact_states.cpp':
        current = b'#include "graph_helpers.cpp"\n'
        original = b'#include "../solver.cpp"\n'
        if content.count(current) != 1:
            raise ValueError('state reconstruction include differs')
        content = content.replace(current, original, 1)
    return hashlib.sha256(content).hexdigest()


def main():
    release = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description='Verification of an extracted certificate package with both checkers.')
    parser.add_argument('--package', type=Path, required=True, help='extracted n11, n12 or n13 package directory')
    parser.add_argument('--build-directory', type=Path, default=release / 'build')
    parser.add_argument('--output', type=Path, help='new verification directory')
    parser.add_argument('--check-only', action='store_true', help='source and build comparison without proof replay')
    for option in ('seconds', 'workers', 'memory-mib', 'max-proof-mib'):
        parser.add_argument('--' + option, type=int)
    args = parser.parse_args()
    if args.output is None and not args.check_only:
        parser.error('--output is required for proof verification')
    try:
        package = args.package.resolve(strict=True)
        release_manifest = json.loads(package_file(release, 'manifest.json').read_text())
        files = release_manifest['files']
        release_file(release, files, 'verify.py')
        certificates = json.loads(release_file(release, files, 'certificates.json').read_text())
        source_paths = certificates['source_paths']
        if not isinstance(source_paths, dict) or not source_paths or \
                any(not isinstance(name, str) or not name.startswith('source/') or not isinstance(path, str)
                    for name, path in source_paths.items()) or len(set(source_paths.values())) != len(source_paths):
            raise ValueError('source paths must be a one-to-one mapping')
        manifest_path = package_file(package, 'manifest.json')
        manifest = json.loads(manifest_path.read_text())
        expected = certificates['packages'][manifest['name']]
        if digest(manifest_path) != expected['manifest_sha256']:
            raise ValueError('package manifest differs from the reviewed release')
        certificate = package_file(package, manifest['certificate']['path'])
        if certificate.stat().st_size != manifest['certificate']['bytes']:
            raise ValueError('certificate file is missing or has the wrong size')
        mapped_sources = {}
        for name, entry in manifest['files'].items():
            if name == manifest['certificate']['path']:
                continue
            path = package_file(package, name)
            if digest(path) != entry['sha256']:
                raise ValueError('package file differs: ' + name)
            legacy = name.startswith('source/')
            if legacy or name == 'trees.txt' or name.startswith(('checkers/', 'reconstruction/')):
                current_name = source_paths[name] if legacy else name
                if current_name in mapped_sources:
                    raise ValueError('duplicate package source: ' + current_name)
                current = release_file(release, files, current_name)
                current_hash = digest(current)
                comparison = source_hash(current, name) if legacy and name != manifest['build']['script'] else current_hash
                if (not legacy or name != manifest['build']['script']) and comparison != entry['sha256']:
                    raise ValueError('release source differs from the package: ' + name)
                mapped_sources[current_name] = current_hash
        target = 'state-verification' if manifest['format'] == 'TPCGST01' else 'placement-verification'
        build = (args.build_directory.resolve(strict=True) / target).resolve(strict=True)
        native = json.loads(package_file(build, 'bin/BUILD.json').read_text())
        if native['status'] != 'built':
            raise ValueError('native build is incomplete')
        if not isinstance(native['source_sha256'], dict) or set(native['source_sha256']) != set(mapped_sources):
            raise ValueError('compiled source inventory differs from the package')
        for name, value in native['source_sha256'].items():
            if value != mapped_sources[name]:
                raise ValueError('compiled source differs from the release: ' + name)
        for name, key in (('compact_states' if target == 'state-verification' else 'witness_codec', 'binary_sha256'),
                          ('check_proof', 'checker_sha256'),
                          ('check_proof_independent', 'independent_checker_sha256')):
            if digest(package_file(build, 'bin/' + name)) != native[key]:
                raise ValueError('compiled binary changed: ' + name)
        for name, expected_hash in native['dependency_sha256'].items():
            if digest(Path(name)) != expected_hash:
                raise ValueError('compiled dependency changed: ' + name)
        if args.check_only:
            print(json.dumps({'status': 'sources_and_build_match', 'package': manifest['name'],
                              'proof_checked': False, 'certificate_hash_checked': False}))
            return
        command = [sys.executable, str(package_file(package, 'verify.py')), '--build-directory', str(build),
                   '--output', str(args.output.resolve())]
        for option in ('seconds', 'workers', 'memory_mib', 'max_proof_mib'):
            value = getattr(args, option)
            if value is not None:
                command += ['--' + option.replace('_', '-'), str(value)]
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.error(str(error))
    os.execv(sys.executable, command)


if __name__ == '__main__':
    main()

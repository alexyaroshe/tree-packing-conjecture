# witness compression build
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import time


CODECS = {'placements': 'placements.cpp'}


def digest(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        while block := stream.read(1024 * 1024):
            value.update(block)
    return value.hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--variant', choices=CODECS, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--compiler', default='clang++')
    parser.add_argument('--cc', default='clang')
    parser.add_argument('--nauty-prefix', type=Path)
    args = parser.parse_args()
    if args.output.exists() or args.output.is_symlink():
        raise RuntimeError('output already exists')
    root = Path(__file__).resolve().parent.parent
    output = args.output.resolve()
    compiler, cc = shutil.which(args.compiler), shutil.which(args.cc)
    if not compiler or not cc:
        raise RuntimeError('C and C++ compilers required')
    names = ('checkers/check_proof.cpp', 'checkers/check_proof_independent.c',
             'reconstruction/' + CODECS[args.variant],
             'reconstruction/build_placements.py', 'reconstruction/verify_placements.py')
    source_hashes = {name: digest(root / name) for name in names}
    compiler_version = subprocess.check_output([compiler, '--version'], text=True, timeout=30)
    cc_version = subprocess.check_output([cc, '--version'], text=True, timeout=30)
    flags = ['-std=c++17', '-O3', '-DNDEBUG', '-Wall', '-Wextra', '-Werror']
    codec_flags = list(flags)
    dependency_hashes = {}
    link_flags = []
    if args.variant == 'placements':
        if args.nauty_prefix is None:
            raise RuntimeError('--nauty-prefix required for placements')
        prefix = args.nauty_prefix.resolve(strict=True)
        include = prefix / 'include/nauty'
        suffix = '.dylib' if platform.system() == 'Darwin' else '.so'
        library = (prefix / 'lib' / ('libnauty' + suffix)).resolve(strict=True)
        if not (include / 'nauty.h').is_file():
            raise RuntimeError('nauty headers required')
        dependency_hashes[str(library)] = digest(library)
        dependency_hashes.update({str(path.resolve()): digest(path) for path in sorted(include.glob('*.h'))})
        codec_flags.extend(['-I', str(include)])
        if 'clang' in compiler_version.lower():
            codec_flags.append('-Wno-c11-extensions')
        link_flags = [str(library), '-Wl,-rpath,' + str(prefix / 'lib')]
    elif args.nauty_prefix is not None:
        raise RuntimeError('nauty is only used by placements')
    output.mkdir(parents=True, exist_ok=False)
    commands = [
        [compiler, *codec_flags, str(root / names[2]), *link_flags, '-o', str(output / 'witness_codec')],
        [compiler, *flags, str(root / 'checkers/check_proof.cpp'), '-o', str(output / 'check_proof')],
        [cc, '-std=c17', '-O3', '-DNDEBUG', '-Wall', '-Wextra', '-Werror',
         str(root / 'checkers/check_proof_independent.c'), '-o', str(output / 'check_proof_independent')],
    ]
    binaries = ('witness_codec', 'check_proof', 'check_proof_independent')
    started = time.monotonic()
    for name, command in zip(binaries, commands):
        with (output / (name + '.build.out')).open('x') as stdout, (output / (name + '.build.err')).open('x') as stderr:
            subprocess.run(command, stdout=stdout, stderr=stderr, check=True, timeout=180)
    if any(digest(root / name) != value for name, value in source_hashes.items()):
        raise RuntimeError('source changed during compilation')
    if any(digest(Path(name)) != value for name, value in dependency_hashes.items()):
        raise RuntimeError('dependency changed during compilation')
    manifest = {
        'status': 'built', 'variant': args.variant, 'created_at': datetime.now(timezone.utc).isoformat(),
        'system': platform.system(), 'machine': platform.machine(),
        'compiler': compiler, 'compiler_version': compiler_version, 'cc': cc, 'cc_version': cc_version,
        'commands': commands, 'source_sha256': source_hashes, 'dependency_sha256': dependency_hashes,
        'binary_sha256': digest(output / 'witness_codec'),
        'checker_sha256': digest(output / 'check_proof'),
        'independent_checker_sha256': digest(output / 'check_proof_independent'),
        'wall_seconds': time.monotonic() - started,
    }
    for name in binaries:
        with (output / name).open('rb') as stream:
            os.fsync(stream.fileno())
    with (output / 'BUILD.json').open('x') as stream:
        json.dump(manifest, stream, indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    descriptor = os.open(output, os.O_RDONLY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    print(json.dumps({'status': 'built', 'variant': args.variant, 'output': str(output),
                      'manifest_sha256': digest(output / 'BUILD.json')}))


if __name__ == '__main__':
    main()

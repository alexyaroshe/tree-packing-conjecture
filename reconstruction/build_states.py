# parallel reconstruction build
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


def digest(path):
    hasher = hashlib.sha256()
    with path.open('rb') as stream:
        while True:
            block = stream.read(1024 * 1024)
            if not block:
                break
            hasher.update(block)
    return hasher.hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--nauty-prefix', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--compiler', default='clang++')
    parser.add_argument('--cc', default='clang')
    args = parser.parse_args()
    if args.output.exists() or args.output.is_symlink():
        raise RuntimeError('output already exists')
    output = args.output.resolve()
    root = Path(__file__).resolve().parent.parent
    prefix = args.nauty_prefix.resolve()
    include = prefix / 'include/nauty'
    library_directory = prefix / 'lib'
    suffix = '.dylib' if platform.system() == 'Darwin' else '.so'
    library = (library_directory / ('libnauty' + suffix)).resolve()
    header = include / 'nauty.h'
    compiler = shutil.which(args.compiler)
    cc = shutil.which(args.cc)
    if not compiler or not cc or not header.is_file() or not library.is_file():
        raise RuntimeError('C/C++ compilers and installed nauty headers/shared library are required')
    names = ('reconstruction/graph_helpers.cpp', 'checkers/check_proof.cpp', 'checkers/check_proof_independent.c', 'trees.txt',
             'reconstruction/state_parallel.cpp', 'reconstruction/build_states.py',
             'reconstruction/verify_states.py')
    source_hashes = {name: digest(root / name) for name in names}
    if source_hashes['checkers/check_proof.cpp'] == source_hashes['checkers/check_proof_independent.c']:
        raise RuntimeError('checker sources must differ')
    dependencies = sorted(include.glob('*.h')) + [library]
    dependency_hashes = {str(path.resolve()): digest(path) for path in dependencies}
    library_hash, header_hash = digest(library), digest(header)
    compiler_version = subprocess.check_output([compiler, '--version'], text=True, timeout=30)
    cc_version = subprocess.check_output([cc, '--version'], text=True, timeout=30)
    output.mkdir(parents=True, exist_ok=False)
    flags = ['-std=c++17', '-O3', '-DNDEBUG', '-Wall', '-Wextra', '-Werror', '-Wno-c11-extensions']
    commands = [
        [compiler, *flags, '-pthread', '-I', str(include), str(root / 'reconstruction/state_parallel.cpp'),
         str(library), '-Wl,-rpath,' + str(library_directory),
         '-o', str(output / 'compact_states')],
        [compiler, *flags, str(root / 'checkers/check_proof.cpp'), '-o', str(output / 'check_proof')],
        [cc, '-std=c17', '-O3', '-DNDEBUG', '-Wall', '-Wextra', '-Werror',
         str(root / 'checkers/check_proof_independent.c'), '-o', str(output / 'check_proof_independent')],
    ]
    started = time.monotonic()
    for name, command in zip(('compact_states', 'check_proof', 'check_proof_independent'), commands):
        with (output / (name + '.build.out')).open('x') as stdout, (output / (name + '.build.err')).open('x') as stderr:
            subprocess.run(command, stdout=stdout, stderr=stderr, check=True, timeout=120)
    if any(digest(root / name) != expected for name, expected in source_hashes.items()):
        raise RuntimeError('source changed during compilation')
    if any(digest(Path(path)) != expected for path, expected in dependency_hashes.items()):
        raise RuntimeError('nauty changed during compilation')
    manifest = {
        'status': 'built', 'created_at': datetime.now(timezone.utc).isoformat(),
        'system': platform.system(), 'machine': platform.machine(), 'source_root': str(root),
        'compiler': compiler, 'compiler_version': compiler_version, 'commands': commands,
        'cc': cc, 'cc_version': cc_version,
        'source_sha256': source_hashes, 'dependency_sha256': dependency_hashes,
        'binary_sha256': digest(output / 'compact_states'),
        'checker_sha256': digest(output / 'check_proof'),
        'independent_checker_sha256': digest(output / 'check_proof_independent'),
        'trees_sha256': source_hashes['trees.txt'],
        'nauty_library': str(library), 'nauty_sha256': library_hash,
        'nauty_header': str(header), 'nauty_header_sha256': header_hash,
        'wall_seconds': time.monotonic() - started,
    }
    for name in ('compact_states', 'check_proof', 'check_proof_independent'):
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
    print(json.dumps({'status': 'built', 'output': str(output), 'manifest_sha256': digest(output / 'BUILD.json')}))


if __name__ == '__main__':
    main()

# full-scope state certificate verifier
# archive hash > bounded state restoration > frozen catalog header > streamer > two checkers > receipt
import argparse
from contextlib import ExitStack
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import select
import shutil
import signal
import struct
import subprocess
import tempfile
import time


TREE_COUNTS = (0, 1, 1, 1, 2, 3, 6, 11, 23, 47, 106, 235, 551, 1301)
cancellation_signal = None
inherited_descriptors = ()


def remaining(deadline):
    if cancellation_signal is not None:
        raise InterruptedError('interrupted by signal ' + str(cancellation_signal))
    seconds = deadline - time.monotonic()
    if seconds <= 0:
        raise TimeoutError('verification deadline exceeded')
    return seconds


def handle_signal(number, frame):
    global cancellation_signal
    cancellation_signal = number


def file_hash(path, deadline):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        while chunk := stream.read(1024 * 1024):
            remaining(deadline)
            digest.update(chunk)
    return digest.hexdigest()


def file_identity(path):
    metadata = path.stat()
    return [metadata.st_dev, metadata.st_ino, metadata.st_size, metadata.st_mtime_ns]


def stop_process(process):
    if process is not None:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        except PermissionError:
            process.wait(timeout=1)
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        process.wait(timeout=5)


def cleanup_processes(processes):
    errors = []
    for process in processes:
        try:
            stop_process(process)
        except (OSError, subprocess.TimeoutExpired) as error:
            errors.append(str(error))
    for process in processes:
        if process is not None:
            for pipe in (process.stdin, process.stdout):
                if pipe is not None:
                    try:
                        pipe.close()
                    except OSError as error:
                        errors.append(str(error))
    return errors


def sync_directory(path):
    descriptor = os.open(path, os.O_RDONLY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def save_receipt(path, value):
    descriptor, temporary = tempfile.mkstemp(prefix=path.name + '.', suffix='.partial', dir=path.parent)
    try:
        with os.fdopen(descriptor, 'w') as stream:
            json.dump(value, stream, indent=2)
            stream.write('\n')
            stream.flush()
            os.fsync(stream.fileno())
        os.link(temporary, path)
    finally:
        os.unlink(temporary)
    sync_directory(path.parent)


def restore_states(command, output, expected_bytes, expected_hash, deadline, record):
    started = time.monotonic()
    restored = output / 'restored.states'
    descriptor, temporary_name = tempfile.mkstemp(prefix='restored.states.', suffix='.partial', dir=output)
    temporary = Path(temporary_name)
    digest = hashlib.sha256()
    count = 0
    process = None
    try:
        with os.fdopen(descriptor, 'wb') as destination, (output / 'decompress.err').open('xb') as errors:
            process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=errors, start_new_session=True, pass_fds=inherited_descriptors)
            os.set_blocking(process.stdout.fileno(), False)
            while True:
                ready, _, _ = select.select([process.stdout], [], [], min(0.25, remaining(deadline)))
                if not ready:
                    continue
                chunk = os.read(process.stdout.fileno(), 1024 * 1024)
                if not chunk:
                    break
                count += len(chunk)
                if count > expected_bytes:
                    raise RuntimeError('restored states exceed expected size')
                digest.update(chunk)
                destination.write(chunk)
            while process.poll() is None:
                time.sleep(min(0.05, remaining(deadline)))
            if process.returncode != 0:
                raise RuntimeError('archive decompression failed')
            if count != expected_bytes or digest.hexdigest() != expected_hash:
                raise RuntimeError('restored states size or SHA-256 differs')
            destination.flush()
            os.fsync(destination.fileno())
        os.link(temporary, restored)
        sync_directory(output)
        return restored
    finally:
        cleanup_errors = cleanup_processes([process])
        try:
            temporary.unlink(missing_ok=True)
        except OSError as error:
            cleanup_errors.append(str(error))
        record.update(exit_code=process.returncode if process is not None else None,
                      states_bytes=count, states_sha256=digest.hexdigest(),
                      wall_seconds=time.monotonic() - started)
        if cleanup_errors:
            record['cleanup_errors'] = cleanup_errors
            raise RuntimeError('decompressor cleanup failed: ' + '; '.join(cleanup_errors))


def catalog_header(path, order, first, last):
    if not 2 <= order <= 13 or not 0 <= first < last <= TREE_COUNTS[order]:
        raise ValueError('invalid assigned range')
    catalog = {}
    level = None
    for line in path.read_text().splitlines():
        fields = line.split()
        if not fields:
            raise RuntimeError('empty catalog line')
        if fields[0] == '#':
            if len(fields) != 2:
                raise RuntimeError('invalid catalog section')
            level = int(fields[1])
            if level not in range(2, 14) or level in catalog:
                raise RuntimeError('duplicate or invalid catalog section')
            catalog[level] = []
        else:
            parents = list(map(int, fields))
            if level is None or len(parents) != level or parents[0] != 0:
                raise RuntimeError('invalid catalog tree')
            if any(parent < 1 or parent > vertex for vertex, parent in enumerate(parents[1:], 1)):
                raise RuntimeError('invalid catalog parent')
            catalog[level].append([parent - 1 for parent in parents[1:]])
    result = bytearray(b'TPCRDP01' + struct.pack('<BHH', order, first, last))
    for level in range(2, order + 1):
        trees = catalog.get(level, [])
        if len(trees) != TREE_COUNTS[level]:
            raise RuntimeError('catalog count differs')
        result.extend(struct.pack('<H', len(trees)))
        for tree in trees:
            result.extend(tree)
    degrees = []
    for tree in catalog[order]:
        degree = [0] * order
        for vertex, parent in enumerate(tree, 1):
            degree[vertex] += 1
            degree[parent] += 1
        degrees.append(max(degree))
    for index in sorted(range(len(degrees)), key=lambda index: -degrees[index])[first:last]:
        result.extend(struct.pack('<H', index))
    return bytes(result)


def check_state_header(states, catalog, order, first, last, expected_bytes):
    expected = b'TPCGST01' + catalog_header(catalog, order, first, last)
    with states.open('rb') as stream:
        if stream.read(len(expected)) != expected:
            raise RuntimeError('compact header differs from frozen catalog or assigned range')
        count_bytes = stream.read(8)
        if len(count_bytes) != 8:
            raise RuntimeError('truncated state count')
        count = struct.unpack('<Q', count_bytes)[0]
    width = (order * (order - 1) // 2 + 7) // 8
    if count >= 2**32 or len(expected) + 8 + count * width != expected_bytes:
        raise RuntimeError('compact state count differs from file size or supported range')
    return count


def check_stream(producer_command, checker_commands, output, deadline, maximum_bytes, record):
    started = time.monotonic()
    producer = None
    checkers = []
    names = ('checker', 'independent_checker')
    digest = hashlib.sha256()
    byte_count, delivered = 0, [0, 0]
    with ExitStack() as logs:
        producer_errors = logs.enter_context((output / 'producer.err').open('xb'))
        checker_logs = [(logs.enter_context((output / (name + '.out')).open('xb')),
                         logs.enter_context((output / (name + '.err')).open('xb'))) for name in names]
        try:
            remaining(deadline)
            producer = subprocess.Popen(producer_command, stdout=subprocess.PIPE, stderr=producer_errors,
                                        start_new_session=True, bufsize=0, pass_fds=inherited_descriptors)
            os.set_blocking(producer.stdout.fileno(), False)
            for command, (verdict, errors) in zip(checker_commands, checker_logs):
                checker = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=verdict,
                                           stderr=errors, start_new_session=True, bufsize=0, pass_fds=inherited_descriptors)
                checkers.append(checker)
                os.set_blocking(checker.stdin.fileno(), False)
            chunk, offsets = b'', [0, 0]
            producer_eof, inputs_closed = False, False
            while True:
                producer_status = producer.poll()
                checker_statuses = [checker.poll() for checker in checkers]
                if producer_status not in (None, 0):
                    raise RuntimeError('producer failed')
                for name, status in zip(names, checker_statuses):
                    if status not in (None, 0):
                        raise RuntimeError(name + ' failed')
                    if status is not None and not inputs_closed:
                        raise RuntimeError(name + ' exited before stream EOF')
                if producer_eof and not chunk and not inputs_closed:
                    for checker in checkers:
                        checker.stdin.close()
                    inputs_closed = True
                if inputs_closed and producer_status == 0 and checker_statuses == [0, 0]:
                    break
                readers = [producer.stdout] if not producer_eof and not chunk else []
                writers = [checker.stdin for index, checker in enumerate(checkers)
                           if chunk and offsets[index] < len(chunk)]
                readable, writable, _ = select.select(readers, writers, [], min(0.25, remaining(deadline)))
                if readable:
                    chunk = os.read(producer.stdout.fileno(), 1024 * 1024)
                    offsets = [0, 0]
                    if chunk:
                        byte_count += len(chunk)
                        if byte_count > maximum_bytes:
                            raise RuntimeError('stream exceeds proof byte limit')
                        digest.update(chunk)
                    else:
                        producer_eof = True
                for index, checker in enumerate(checkers):
                    if checker.stdin in writable:
                        try:
                            written = os.write(checker.stdin.fileno(), memoryview(chunk)[offsets[index]:])
                        except BlockingIOError:
                            continue
                        if written <= 0:
                            raise RuntimeError(names[index] + ' pipe stopped accepting bytes')
                        offsets[index] += written
                        delivered[index] += written
                if chunk and all(offset == len(chunk) for offset in offsets):
                    chunk = b''
        finally:
            cleanup_errors = cleanup_processes([*checkers, producer])
            record.update(producer_exit=producer.returncode if producer is not None else None,
                          checker_exits={name: checker.returncode for name, checker in zip(names, checkers)},
                          proof_bytes=byte_count, proof_sha256=digest.hexdigest(),
                          delivered_bytes=dict(zip(names, delivered)),
                          wall_seconds=time.monotonic() - started)
            if cleanup_errors:
                record['cleanup_errors'] = cleanup_errors
                raise RuntimeError('stream cleanup failed: ' + '; '.join(cleanup_errors))
    record['statistics'] = json.loads((output / 'producer.err').read_text())
    record['verdicts'] = {name: json.loads((output / (name + '.out')).read_text()) for name in names}


def sha256_argument(value):
    value = value.lower()
    if len(value) != 64 or any(character not in '0123456789abcdef' for character in value):
        raise argparse.ArgumentTypeError('SHA-256 requires 64 hexadecimal digits')
    return value


def main():
    parser = argparse.ArgumentParser()
    for name in ('archive', 'streamer', 'checker', 'independent-checker', 'trees', 'output'):
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--expected-archive-sha256', type=sha256_argument, required=True)
    parser.add_argument('--expected-states-sha256', type=sha256_argument, required=True)
    parser.add_argument('--expected-states-bytes', type=int, required=True)
    parser.add_argument('--n', type=int, choices=range(2, 14), required=True)
    parser.add_argument('--top-first', type=int, required=True)
    parser.add_argument('--top-last', type=int, required=True)
    parser.add_argument('--expected-proof-sha256', type=sha256_argument)
    parser.add_argument('--seconds', type=int, default=3600)
    parser.add_argument('--memory-mib', type=int, default=4096, help='expander memory limit')
    parser.add_argument('--max-proof-mib', type=int, default=32768)
    parser.add_argument('--lock-fd', type=int, help=argparse.SUPPRESS)
    args = parser.parse_args()
    global inherited_descriptors
    if args.lock_fd is not None:
        if args.lock_fd < 0:
            parser.error('invalid inherited lock descriptor')
        os.fstat(args.lock_fd)
        inherited_descriptors = (args.lock_fd,)
    if min(args.seconds, args.memory_mib, args.max_proof_mib, args.expected_states_bytes) <= 0:
        parser.error('limits and expected state size must be positive')
    if not 0 <= args.top_first < args.top_last <= TREE_COUNTS[args.n]:
        parser.error('invalid assigned range')
    paths = {name: getattr(args, name).resolve(strict=True)
             for name in ('archive', 'streamer', 'checker', 'independent_checker', 'trees')}
    if any(not path.is_file() for path in paths.values()):
        parser.error('inputs must be regular files')
    if paths['checker'].samefile(paths['independent_checker']):
        parser.error('two distinct checker binaries are required')
    zstd = shutil.which('zstd')
    if zstd is None:
        parser.error('zstd executable missing')
    paths['zstd'] = Path(zstd).resolve(strict=True)
    paths['verifier'] = Path(__file__).resolve(strict=True)
    signal.signal(signal.SIGTERM, handle_signal)
    signal.signal(signal.SIGINT, handle_signal)
    if args.output.is_symlink():
        parser.error('output must be a new directory, not a symlink')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    started = time.monotonic()
    deadline = started + args.seconds
    scope = {'n': args.n, 'top_first': args.top_first, 'top_last': args.top_last}
    roots = args.top_last - args.top_first
    restored = output / 'restored.states'
    commands = {
        'decompress': [str(paths['zstd']), '-q', '-dc', str(paths['archive'])],
        'producer': [str(paths['streamer']), 'stream', str(restored), '--seconds', str(args.seconds),
                     '--memory-mib', str(args.memory_mib), '--max-output-mib', str(args.max_proof_mib)],
        'checker': [str(paths['checker']), '/dev/stdin', '--seconds', str(args.seconds),
                    '--max-mib', str(args.max_proof_mib)],
        'independent_checker': [str(paths['independent_checker']), '/dev/stdin', '--seconds', str(args.seconds),
                                '--max-mib', str(args.max_proof_mib)]}
    record = {'status': 'running', 'started_at': datetime.now(timezone.utc).isoformat(),
              'scope': scope, 'expected_states_bytes': args.expected_states_bytes,
              'expected_states_sha256': args.expected_states_sha256,
              'expected_archive_sha256': args.expected_archive_sha256, 'commands': commands,
              'expected_proof_sha256': args.expected_proof_sha256,
              'proof_hash_bound': args.expected_proof_sha256 is not None,
              'limits': {'seconds': args.seconds, 'memory_mib': args.memory_mib, 'max_proof_mib': args.max_proof_mib},
              'inputs': {}, 'restore': {}, 'stream': {}, 'raw_proof_saved': False}
    save_receipt(output / 'plan.json', record)
    try:
        for name, path in paths.items():
            record['inputs'][name] = {'path': str(path), 'identity': file_identity(path),
                                      'sha256': file_hash(path, deadline)}
        if record['inputs']['archive']['sha256'] != args.expected_archive_sha256:
            raise RuntimeError('archive SHA-256 differs')
        if record['inputs']['checker']['sha256'] == record['inputs']['independent_checker']['sha256']:
            raise RuntimeError('checker binaries have identical SHA-256')
        restore_states(commands['decompress'], output, args.expected_states_bytes, args.expected_states_sha256,
                       deadline, record['restore'])
        count = check_state_header(restored, paths['trees'], args.n, args.top_first, args.top_last,
                                   args.expected_states_bytes)
        check_stream(commands['producer'], [commands['checker'], commands['independent_checker']],
                     output, deadline, args.max_proof_mib * 1024**2, record['stream'])
        statistics, verdicts = record['stream']['statistics'], record['stream']['verdicts']
        expected_statistics = {**scope, 'status': 'streamed', 'states': count, 'input_bytes': args.expected_states_bytes}
        expected_verdict = {**scope, 'status': 'verified', 'roots': roots, 'nodes': count}
        if any(type(statistics.get(key)) is not type(value) or statistics.get(key) != value
               for key, value in expected_statistics.items()):
            raise RuntimeError('producer statistics differ from compact certificate')
        for name, verdict in verdicts.items():
            if any(type(verdict.get(key)) is not type(value) or verdict.get(key) != value
                   for key, value in expected_verdict.items()):
                raise RuntimeError(name + ' verdict differs from assigned range')
            if type(verdict.get('placements')) is not int or verdict['placements'] < roots:
                raise RuntimeError(name + ' placement count invalid')
            if type(verdict.get('proof_bytes')) is not int or verdict['proof_bytes'] <= 0:
                raise RuntimeError(name + ' proof byte count invalid')
        verdict = verdicts['checker']
        fields = (*expected_verdict, 'placements', 'proof_bytes')
        if any(verdict.get(key) != verdicts['independent_checker'].get(key) for key in fields):
            raise RuntimeError('checker verdicts disagree')
        proof_bytes = verdict.get('proof_bytes')
        if type(proof_bytes) is not int or not 0 < proof_bytes <= args.max_proof_mib * 1024**2 or \
                type(statistics.get('output_bytes')) is not int or statistics['output_bytes'] != proof_bytes or \
                record['stream']['proof_bytes'] != proof_bytes or \
                any(count != proof_bytes for count in record['stream']['delivered_bytes'].values()):
            raise RuntimeError('producer, fanout and checker proof byte counts differ')
        if args.expected_proof_sha256 is not None and record['stream']['proof_sha256'] != args.expected_proof_sha256:
            raise RuntimeError('reconstructed proof SHA-256 differs')
        if file_hash(restored, deadline) != args.expected_states_sha256:
            raise RuntimeError('restored states changed during verification')
        for name, path in paths.items():
            previous = record['inputs'][name]
            if previous['identity'] != file_identity(path) or previous['sha256'] != file_hash(path, deadline):
                raise RuntimeError('input changed during verification: ' + name)
        remaining(deadline)
        record.update(status='verified', states=count, proof_bytes=proof_bytes,
                      proof_sha256=record['stream']['proof_sha256'])
    except (Exception, KeyboardInterrupt) as error:
        record.update(status='failed', error=str(error) or type(error).__name__)
    record['wall_seconds'] = time.monotonic() - started
    record['finished_at'] = datetime.now(timezone.utc).isoformat()
    record['logs_sha256'] = {path.name: hashlib.sha256(path.read_bytes()).hexdigest()
                            for path in output.iterdir() if path.suffix in ('.out', '.err')}
    save_receipt(output / 'finished.json', record)
    print(json.dumps(record))
    return 0 if record['status'] == 'verified' else 1


if __name__ == '__main__':
    raise SystemExit(main())

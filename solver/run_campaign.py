# parallel-state campaign runner
# frozen plan > shared solver/checkpoint > states > zstd > restoration & two checkers > verified receipt
# resume: immutable bindings > completed phase hashes | checkpoint > remaining phases
# export: committed inode > bounded copy & inspection > origin accounting; import > fresh plan & working checkpoint
import argparse
from contextlib import ExitStack
from datetime import datetime, timezone
import fcntl
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time


TREE_COUNTS = (0, 1, 1, 1, 2, 3, 6, 11, 23, 47, 106, 235, 551, 1301)
cancellation_signal = None


class Incomplete(RuntimeError):
    pass


def interrupt(number, frame):
    global cancellation_signal
    cancellation_signal = number


def check(deadline):
    if cancellation_signal is not None:
        raise Incomplete('interrupted by signal ' + str(cancellation_signal))
    if time.time() >= deadline:
        raise Incomplete('campaign deadline reached')


def digest(path, deadline=None):
    if path.is_symlink() or not path.is_file():
        raise RuntimeError('regular file required: ' + str(path))
    value = hashlib.sha256()
    with path.open('rb') as stream:
        while block := stream.read(1024 * 1024):
            if deadline is not None:
                check(deadline)
            value.update(block)
    return value.hexdigest()


def file_record(path, deadline=None):
    return {'bytes': path.stat().st_size, 'sha256': digest(path, deadline)}


def sync_directory(path):
    descriptor = os.open(path, os.O_RDONLY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def save(path, value, replace=False):
    descriptor, name = tempfile.mkstemp(prefix=path.name + '.', suffix='.partial', dir=path.parent)
    temporary = Path(name)
    try:
        with os.fdopen(descriptor, 'w') as stream:
            json.dump(value, stream, indent=2)
            stream.write('\n')
            stream.flush()
            os.fsync(stream.fileno())
        if replace:
            os.replace(temporary, path)
        else:
            os.link(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)
    sync_directory(path.parent)


def load(path):
    if path.is_symlink() or not path.is_file() or path.stat().st_size > 16 * 1024**2:
        raise RuntimeError('invalid receipt: ' + str(path))
    return json.loads(path.read_text())


def bind_inputs(build, trees):
    manifest = load(build / 'BUILD.json')
    source = Path(manifest['source_root']).resolve(strict=True)
    bindings = {}
    for name, wanted in manifest['source_sha256'].items():
        path = (source / name).resolve(strict=True)
        if not path.is_relative_to(source) or digest(path) != wanted:
            raise RuntimeError('build source differs: ' + name)
        bindings[str(path)] = file_record(path)
    for name, key in (('solver', 'solver_sha256'), ('compact_states', 'binary_sha256'),
                      ('check_proof', 'checker_sha256'), ('check_proof_independent', 'independent_checker_sha256')):
        path = build / name
        if digest(path) != manifest[key]:
            raise RuntimeError('build binary differs: ' + name)
        bindings[str(path)] = file_record(path)
    if manifest['checker_sha256'] == manifest['independent_checker_sha256']:
        raise RuntimeError('two distinct checkers required')
    for name, wanted in manifest['dependency_sha256'].items():
        path = Path(name)
        if digest(path) != wanted:
            raise RuntimeError('build dependency differs: ' + name)
        bindings[str(path)] = file_record(path)
    if digest(trees) != manifest['trees_sha256']:
        raise RuntimeError('catalog differs from build')
    compressor = shutil.which('zstd')
    if compressor is None:
        raise RuntimeError('zstd required')
    for path in (trees, build / 'BUILD.json', Path(__file__).resolve(), Path(compressor).resolve()):
        bindings[str(path)] = file_record(path)
    return source, Path(compressor).resolve(), bindings


def verify_bindings(plan, deadline):
    for name, expected in plan['bindings'].items():
        if file_record(Path(name), deadline) != expected:
            raise RuntimeError('frozen input changed: ' + name)


def check_plan(root):
    if digest(root / 'plan.json') != load(root / 'campaign.json')['plan_sha256']:
        raise RuntimeError('campaign plan changed')


def process_identity(pid):
    try:
        return (Path('/proc') / str(pid) / 'stat').read_text().rpartition(') ')[2].split()[19]
    except FileNotFoundError:
        return 'absent' if Path('/proc').is_dir() else None


def same_group(group, identity):
    try:
        os.killpg(group, 0)
    except ProcessLookupError:
        return False
    return identity is None or process_identity(group) == identity


def sample_tree(process, groups):
    for group, identity in list(groups.items()):
        if not same_group(group, identity):
            del groups[group]
    if process.poll() is not None:
        return {}
    pending, seen, samples = [process.pid], set(), {}
    while pending:
        pid = pending.pop()
        if pid in seen:
            continue
        seen.add(pid)
        path = Path('/proc') / str(pid)
        try:
            pending.extend(map(int, (path / 'task' / str(pid) / 'children').read_text().split()))
            status = dict(line.split(':', 1) for line in (path / 'status').read_text().splitlines())
            samples[str(pid)] = {'name': status['Name'].strip(),
                                 'rss_bytes': int(status.get('VmRSS', '0 kB').split()[0]) * 1024,
                                 'observed_high_water_rss_bytes': int(status.get('VmHWM', '0 kB').split()[0]) * 1024}
            if os.getpgid(pid) == pid:
                groups[pid] = process_identity(pid)
        except (FileNotFoundError, ProcessLookupError):
            continue
    return samples


def stop(process, groups, graceful):
    sample_tree(process, groups)
    if process.poll() is None and graceful:
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            process.wait(timeout=90)
        except subprocess.TimeoutExpired:
            pass
    for group, identity in groups.items():
        if not same_group(group, identity):
            continue
        try:
            os.killpg(group, signal.SIGKILL)
        except ProcessLookupError:
            pass
        except PermissionError:
            process.poll()
            try:
                os.killpg(group, signal.SIGKILL)
            except ProcessLookupError:
                pass
    process.wait(timeout=10)


def storage(root, limits):
    free = shutil.disk_usage(root).free
    seen, allocated = set(), 0
    for path in root.rglob('*'):
        if not path.is_file():
            continue
        status = path.stat()
        identity = (status.st_dev, status.st_ino)
        if identity not in seen:
            seen.add(identity)
            allocated += status.st_blocks * 512
    if free < limits['minimum_free_mib'] * 1024**2 or allocated > limits['maximum_disk_mib'] * 1024**2:
        raise Incomplete('disk budget reached')
    return free, allocated


def phase(root, attempt, name, command, seconds, plan, lock_descriptor):
    check_plan(root)
    verify_bindings(plan, plan['deadline_epoch'])
    check(plan['deadline_epoch'])
    storage(root, plan['limits'])
    began, epoch = time.monotonic(), time.time()
    process, groups = None, {}
    result = {'command': command, 'sample_interval_seconds': 0.2,
              'sampled_peak_process_tree_rss_bytes': 0, 'sampled_process_peaks': {},
              'minimum_free_bytes': shutil.disk_usage(root).free, 'maximum_allocated_bytes': 0}
    error = None
    try:
        with (attempt / (name + '.out')).open('xb') as stdout, (attempt / (name + '.err')).open('xb') as stderr:
            process = subprocess.Popen(command, stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr,
                                       start_new_session=True, pass_fds=(lock_descriptor,))
            groups[process.pid] = process_identity(process.pid)
            save(attempt / (name + '.started.json'), {'command': command, 'pid': process.pid,
                                                     'started_epoch': epoch, 'seconds': seconds})
            next_storage = 0
            while process.poll() is None:
                sample = sample_tree(process, groups)
                total = sum(item['rss_bytes'] for item in sample.values())
                result['sampled_peak_process_tree_rss_bytes'] = max(result['sampled_peak_process_tree_rss_bytes'], total)
                for pid, value in sample.items():
                    prior = result['sampled_process_peaks'].get(pid, {'rss_bytes': 0, 'observed_high_water_rss_bytes': 0})
                    result['sampled_process_peaks'][pid] = {
                        'name': value['name'], 'rss_bytes': max(prior['rss_bytes'], value['rss_bytes']),
                        'observed_high_water_rss_bytes': max(prior['observed_high_water_rss_bytes'], value['observed_high_water_rss_bytes'])}
                if total > plan['limits']['aggregate_memory_mib'] * 1024**2:
                    raise Incomplete('aggregate memory budget reached')
                check(min(plan['deadline_epoch'], epoch + seconds + 30))
                if time.monotonic() >= next_storage:
                    check_plan(root)
                    free, allocated = storage(root, plan['limits'])
                    result['minimum_free_bytes'] = min(result['minimum_free_bytes'], free)
                    result['maximum_allocated_bytes'] = max(result['maximum_allocated_bytes'], allocated)
                    next_storage = time.monotonic() + 1
                time.sleep(0.2)
    except Exception as caught:
        error = caught
    finally:
        if process is not None:
            try:
                stop(process, groups, graceful=error is not None)
            except (OSError, subprocess.TimeoutExpired) as caught:
                error = RuntimeError('child cleanup failed: ' + str(caught))
            result.update(exit_code=process.returncode, wall_seconds=time.monotonic() - began)
        else:
            result.update(exit_code=None, wall_seconds=time.monotonic() - began)
        result['logs'] = {suffix: file_record(attempt / (name + '.' + suffix))
                          for suffix in ('out', 'err') if (attempt / (name + '.' + suffix)).exists()}
        if error is not None:
            result['error'] = str(error)
        save(attempt / (name + '.finished.json'), result)
    if error is not None:
        raise error
    check_plan(root)
    verify_bindings(plan, plan['deadline_epoch'])
    return result


def marker(root, name, value=None):
    check_plan(root)
    path = root / ('phase-' + name + '.json')
    if value is not None:
        value = {**value, 'plan_sha256': digest(root / 'plan.json')}
        save(path, value)
    if not path.exists():
        return None
    result = load(path)
    if result['plan_sha256'] != digest(root / 'plan.json'):
        raise RuntimeError('phase plan binding differs')
    for relative, expected in result['artifacts'].items():
        artifact = root / relative
        if not artifact.resolve().is_relative_to(root) or file_record(artifact) != expected:
            raise RuntimeError('completed phase artifact differs: ' + relative)
    return result


def state_metadata(root, plan, verifier):
    states = root / 'packing.states'
    record = file_record(states, plan['deadline_epoch'])
    count = verifier.check_state_header(states, Path(plan['trees']), plan['n'], 0,
                                        TREE_COUNTS[plan['n']], record['bytes'])
    return {**record, 'nodes': count}


def verification_receipt(root, plan, states, archive, path):
    receipt = load(path)
    scope = {'n': plan['n'], 'top_first': 0, 'top_last': TREE_COUNTS[plan['n']]}
    expected = {**scope, 'status': 'verified', 'roots': TREE_COUNTS[plan['n']], 'nodes': states['nodes']}
    if receipt['status'] != 'verified' or receipt['scope'] != scope or receipt['raw_proof_saved'] is not False:
        raise RuntimeError('verification scope or status differs')
    if receipt['expected_states_sha256'] != states['sha256'] or receipt['expected_archive_sha256'] != archive['sha256']:
        raise RuntimeError('verification input binding differs')
    stream = receipt['stream']
    verdicts = stream['verdicts']
    if set(verdicts) != {'checker', 'independent_checker'} or verdicts['checker'] != verdicts['independent_checker']:
        raise RuntimeError('both checker verdicts required')
    if any(type(verdicts['checker'].get(key)) is not type(value) or verdicts['checker'].get(key) != value
           for key, value in expected.items()):
        raise RuntimeError('checker full coverage differs')
    if stream['producer_exit'] != 0 or stream['checker_exits'] != {'checker': 0, 'independent_checker': 0}:
        raise RuntimeError('verification process failed')
    if set(stream['delivered_bytes'].values()) != {receipt['proof_bytes']} or stream['proof_bytes'] != receipt['proof_bytes']:
        raise RuntimeError('incomplete proof delivery')
    for name in ('checker', 'independent_checker', 'streamer', 'verifier', 'trees', 'archive'):
        actual = receipt['inputs'][name]
        expected_hash = archive['sha256'] if name == 'archive' else plan['bindings'][actual['path']]['sha256']
        if actual['sha256'] != expected_hash:
            raise RuntimeError('verified input differs: ' + name)
    for name, wanted in receipt['logs_sha256'].items():
        if digest(path.parent / name) != wanted:
            raise RuntimeError('verification log differs: ' + name)
    return receipt


def remaining_solver_seconds(root, plan):
    spent = plan.get('inherited_solver_seconds', 0)
    for path in (root / 'attempts').glob('*/solve.started.json'):
        finished = path.with_name('solve.finished.json')
        spent += load(finished)['wall_seconds'] if finished.exists() else max(0, time.time() - load(path)['started_epoch'])
    remaining = plan['limits']['solver_seconds'] - spent
    if remaining <= 0:
        raise Incomplete('cumulative solver time budget reached')
    return remaining


def verifier_module(source):
    spec = importlib.util.spec_from_file_location('campaign_verifier', source / 'reconstruction/verify_serial.py')
    verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verifier)
    return verifier


def copy_checkpoint(source, destination, maximum_bytes, deadline, expected=None):
    check(deadline)
    descriptor = os.open(source, os.O_RDONLY | os.O_NOFOLLOW)
    temporary_descriptor, name = tempfile.mkstemp(prefix=destination.name + '.', suffix='.partial', dir=destination.parent)
    temporary = Path(name)
    value, count = hashlib.sha256(), 0
    try:
        with os.fdopen(descriptor, 'rb') as incoming, os.fdopen(temporary_descriptor, 'wb') as outgoing:
            before = os.fstat(incoming.fileno())
            if not stat.S_ISREG(before.st_mode) or before.st_size > maximum_bytes:
                raise RuntimeError('checkpoint is not a bounded regular file')
            while block := incoming.read(1024 * 1024):
                check(deadline)
                count += len(block)
                if count > maximum_bytes:
                    raise RuntimeError('checkpoint exceeds copy limit')
                outgoing.write(block)
                value.update(block)
            after = os.fstat(incoming.fileno())
            if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) != \
                    (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns) or count != before.st_size:
                raise RuntimeError('opened checkpoint inode changed during copy')
            record = {'bytes': count, 'sha256': value.hexdigest()}
            if expected is not None and record != expected:
                raise RuntimeError('import checkpoint differs from provenance')
            outgoing.flush()
            os.fsync(outgoing.fileno())
        os.link(temporary, destination)
        sync_directory(destination.parent)
        return record
    finally:
        temporary.unlink(missing_ok=True)


def inspect_checkpoint(build, checkpoint, plan, maximum_bytes, deadline):
    seconds = min(3600, deadline - time.time())
    if seconds <= 0:
        raise Incomplete('checkpoint inspection deadline reached')
    command = [str(build / 'solver'), '--inspect-checkpoint', str(checkpoint),
               '--n', str(plan['n']), '--trees', plan['trees'], '--top', f"0:{TREE_COUNTS[plan['n']]}",
               '--max-output-mib', str((maximum_bytes + 1024**2 - 1) // 1024**2), '--seconds', str(seconds)]
    result = subprocess.run(command, stdin=subprocess.DEVNULL, capture_output=True, timeout=seconds + 10)
    if result.returncode:
        raise RuntimeError('checkpoint inspection failed: ' + result.stderr.decode(errors='replace')[-1000:])
    inspection = json.loads(result.stdout)
    expected = {'status': 'valid', 'n': plan['n'], 'top_first': 0, 'top_last': TREE_COUNTS[plan['n']],
                'checkpoint_bytes': checkpoint.stat().st_size, 'checksum_valid': True,
                'root_children_checked': True, 'duplicate_states_checked': False,
                'orbits': True, 'siblings': True, 'cache_bits': 18}
    if any(type(inspection.get(key)) is not type(value) or inspection.get(key) != value for key, value in expected.items()):
        raise RuntimeError('checkpoint inspection scope or checksum differs')
    completed = inspection.get('completed')
    if type(completed) is not int or not 0 <= completed <= expected['top_last']:
        raise RuntimeError('checkpoint completed prefix invalid')
    counts = [inspection.get(name) for name in ('stored_states', 'good_states', 'bad_states')]
    if any(type(count) is not int or count < 0 for count in counts) or counts[0] != counts[1] + counts[2]:
        raise RuntimeError('checkpoint memo counts invalid')
    return inspection


def accounting(root, plan, snapshot_epoch, captured=None):
    if not math.isfinite(snapshot_epoch) or snapshot_epoch <= 0:
        raise RuntimeError('invalid checkpoint snapshot time')
    inherited = plan.get('inherited_solver_seconds', 0)
    if not math.isfinite(inherited) or inherited < 0:
        raise RuntimeError('invalid inherited solver accounting')
    attempts, spent = {}, inherited
    for started_path in sorted((root / 'attempts').glob('*/solve.started.json')):
        started = load(started_path)
        epoch = started['started_epoch']
        if not math.isfinite(epoch) or epoch <= 0:
            raise RuntimeError('invalid origin solver start time')
        if epoch > snapshot_epoch:
            continue
        relative = started_path.relative_to(root).as_posix()
        evidence = {'started': file_record(started_path)}
        finished_path = started_path.with_name('solve.finished.json')
        if captured is None:
            finished_record = file_record(finished_path) if finished_path.exists() else None
        else:
            if relative not in captured:
                raise RuntimeError('origin attempt omitted from provenance')
            finished_record = captured[relative]['finished']
        if finished_record is not None:
            if file_record(finished_path) != finished_record:
                raise RuntimeError('origin solver receipt changed')
            elapsed = load(finished_path)['wall_seconds']
        else:
            elapsed = max(0, snapshot_epoch - epoch)
        if not math.isfinite(elapsed) or elapsed < 0:
            raise RuntimeError('invalid origin solver elapsed time')
        evidence.update(finished=finished_record, charged_seconds=elapsed)
        attempts[relative] = evidence
        spent += elapsed
    if captured is not None and attempts != captured:
        raise RuntimeError('origin accounting differs from provenance')
    return spent, attempts


def origin_evidence(root):
    check_plan(root)
    plan = load(root / 'plan.json')
    verify_bindings(plan, None)
    return plan, {'campaign': str(root), 'plan': file_record(root / 'plan.json'),
                  'commit': file_record(root / 'campaign.json'), 'build': file_record(Path(plan['build']) / 'BUILD.json')}


def origin_lock_state(root, stack, allow_active):
    for name in ('campaign.lock', 'checkpoint.bin.lock'):
        path = root / name
        if path.is_symlink() or not path.is_file():
            raise RuntimeError('origin lock missing or invalid')
        handle = stack.enter_context(path.open('rb'))
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            if not allow_active:
                raise RuntimeError('handoff requires inactive origin campaign and solver')
            return True
    return False


def mathematical_source(manifest, name, legacy_name):
    sources = manifest['source_sha256']
    candidates = {name, legacy_name}.intersection(sources)
    if len(candidates) != 1:
        raise RuntimeError('import source identity missing or ambiguous: ' + name)
    selected = candidates.pop()
    root = Path(manifest['source_root']).resolve(strict=True)
    path = root / selected
    if path.is_symlink() or not path.resolve(strict=True).is_relative_to(root):
        raise RuntimeError('import source outside build root: ' + name)
    content = path.read_bytes()
    if hashlib.sha256(content).hexdigest() != sources[selected]:
        raise RuntimeError('import build source changed: ' + name)
    prefix = b'#' if path.suffix == '.py' else b'//'
    lines = content.splitlines(keepends=True)
    for index, line in enumerate(lines):
        if not line.startswith(prefix):
            break
        lines[index] = line.replace(b' > ', b' -> ')
    content = b''.join(lines)
    if name == 'reconstruction/state_serial.cpp':
        old = b'#include "../solver.cpp"\n'
        new = b'#include "graph_helpers.cpp"\n'
        expected, other = (old, new) if selected == legacy_name else (new, old)
        if content.count(expected) != 1 or other in content:
            raise RuntimeError('import reconstruction include differs')
        content = content.replace(expected, new, 1)
    return content


def compatible_build(build, origin_plan):
    original = load(Path(origin_plan['build']) / 'BUILD.json')
    proposed = load(build / 'BUILD.json')
    source = Path(proposed['source_root']).resolve(strict=True)
    mapping_path = source / 'certificates.json'
    if digest(mapping_path) != proposed['source_sha256'].get('certificates.json'):
        raise RuntimeError('import source mapping changed')
    source_paths = load(mapping_path)['source_paths']
    if not isinstance(source_paths, dict):
        raise RuntimeError('invalid import source mapping')
    legacy_paths = {}
    for legacy, current in source_paths.items():
        if not isinstance(legacy, str) or not isinstance(current, str) or not legacy.startswith('source/') or \
                Path(current).is_absolute() or '..' in Path(legacy).parts or '..' in Path(current).parts or \
                current in legacy_paths:
            raise RuntimeError('invalid import source mapping')
        legacy_paths[current] = legacy[len('source/'):]
    for name in ('trees.txt', 'reconstruction/graph_helpers.cpp', 'reconstruction/state_serial.cpp', 'reconstruction/verify_serial.py',
                 'checkers/check_proof.cpp', 'checkers/check_proof_independent.c'):
        if name not in legacy_paths or \
                mathematical_source(original, name, legacy_paths[name]) != \
                mathematical_source(proposed, name, legacy_paths[name]):
            raise RuntimeError('import mathematical dependency differs: ' + name)
    if original['dependency_sha256'] != proposed['dependency_sha256']:
        raise RuntimeError('import nauty dependency differs')


def validate_import(checkpoint, provenance_path, build, order, solver_cap, mode, stack):
    commit = load(provenance_path.parent / 'export.json')
    if commit.get('status') != 'exported' or commit.get('provenance') != file_record(provenance_path):
        raise RuntimeError('checkpoint export commit differs from provenance')
    provenance = load(provenance_path)
    if provenance.get('schema') != 'TPCMEM01-export-v1':
        raise RuntimeError('unsupported checkpoint provenance')
    if provenance['snapshot_epoch'] != commit['snapshot_epoch'] or not \
            0 < commit['started_epoch'] <= commit['snapshot_epoch'] <= commit['completed_epoch'] <= time.time() + 1:
        raise RuntimeError('checkpoint export snapshot time differs')
    origin = Path(provenance['origin']['campaign']).resolve(strict=True)
    origin_lock_state(origin, stack, allow_active=mode == 'benchmark')
    original, evidence = origin_evidence(origin)
    if evidence != provenance['origin'] or original['n'] != order:
        raise RuntimeError('checkpoint origin binding or order differs')
    compatible_build(build, original)
    spent, attempts = accounting(origin, original, provenance['snapshot_epoch'], provenance['attempts'])
    if not attempts:
        raise RuntimeError('checkpoint export lacks an origin solver attempt')
    if mode == 'handoff':
        if (original.get('imported_checkpoint') or {}).get('mode') == 'benchmark':
            raise RuntimeError('benchmark lineage cannot become a production handoff')
        if provenance['origin_active'] or any(value['finished'] is None for value in attempts.values()):
            raise RuntimeError('handoff requires a fresh inactive export with final solver receipts')
        current_spent, current_attempts = accounting(origin, original, time.time())
        if current_spent != spent or current_attempts != attempts or file_record(origin / 'checkpoint.bin') != provenance['checkpoint']:
            raise RuntimeError('handoff origin advanced after checkpoint export')
    limits = provenance['accounting']
    expected = {'solver_seconds_spent': spent, 'solver_seconds_cap': original['limits']['solver_seconds'],
                'deadline_epoch': original['deadline_epoch']}
    if limits != expected:
        raise RuntimeError('checkpoint budget provenance differs')
    if solver_cap > limits['solver_seconds_cap'] or solver_cap <= spent:
        raise RuntimeError('import solver cap must exceed inherited spend without increasing origin cap')
    if file_record(checkpoint) != provenance['checkpoint']:
        raise RuntimeError('import checkpoint differs from provenance')
    return provenance, original


def export_checkpoint(args):
    root = args.output.resolve(strict=True)
    destination = args.destination.resolve()
    if args.destination.is_symlink() or destination.exists() or args.seconds <= 0:
        raise RuntimeError('new export directory and positive time limit required')
    started_epoch = time.time()
    deadline = started_epoch + args.seconds
    with ExitStack() as locks:
        active = origin_lock_state(root, locks, allow_active=True)
        original, evidence = origin_evidence(root)
        build = args.build.resolve(strict=True)
        source, compressor, bindings = bind_inputs(build, Path(original['trees']))
        compatible_build(build, original)
        destination.mkdir(parents=True, exist_ok=False)
        checkpoint = destination / 'checkpoint.bin'
        record = copy_checkpoint(root / 'checkpoint.bin', checkpoint,
                                 original['limits']['max_state_mib'] * 1024**2, deadline)
        snapshot_epoch = time.time()
        spent, attempts = accounting(root, original, snapshot_epoch)
        if not attempts:
            raise RuntimeError('checkpoint export lacks an origin solver attempt')
        inspection = inspect_checkpoint(build, checkpoint, original, record['bytes'], deadline)
        if origin_evidence(root)[1] != evidence:
            raise RuntimeError('checkpoint origin changed during export')
        if file_record(checkpoint, deadline) != record:
            raise RuntimeError('export checkpoint changed during inspection')
        verify_bindings({'bindings': bindings}, deadline)
        provenance = {'schema': 'TPCMEM01-export-v1', 'snapshot_epoch': snapshot_epoch,
                      'origin_active': active, 'origin': evidence, 'checkpoint': record, 'inspection': inspection,
                      'attempts': attempts, 'accounting': {'solver_seconds_spent': spent,
                          'solver_seconds_cap': original['limits']['solver_seconds'], 'deadline_epoch': original['deadline_epoch']},
                      'inspector': {'path': str(build / 'solver'), **file_record(build / 'solver')}}
        save(destination / 'provenance.json', provenance)
        save(destination / 'export.json', {'status': 'exported', 'started_epoch': started_epoch,
                                           'snapshot_epoch': snapshot_epoch, 'completed_epoch': time.time(),
                                           'provenance': file_record(destination / 'provenance.json')})
        print(json.dumps({'status': 'exported', 'destination': str(destination), 'origin_active': active,
                          'checkpoint': record, 'completed': inspection['completed'], 'stored_states': inspection['stored_states']}))
        return 0


def execute(root, plan, lock_descriptor):
    check_plan(root)
    deadline = None if (root / 'finished.json').exists() else plan['deadline_epoch']
    verify_bindings(plan, deadline)
    build, source = Path(plan['build']), Path(plan['source'])
    verifier_path = source / 'reconstruction/verify_serial.py'
    verifier = verifier_module(source)
    if plan['n'] == 13 and plan['n13_on_hold']:
        raise RuntimeError('n13 campaign remains on hold')
    solved, compressed, verified = (marker(root, name) for name in ('solve', 'compress', 'verify'))
    if (root / 'finished.json').exists():
        final = load(root / 'finished.json')
        if not all((solved, compressed, verified)) or final['status'] != 'verified':
            raise RuntimeError('invalid final campaign receipt')
        receipt = verification_receipt(root, plan, solved['states'], compressed['archive'], root / verified['receipt'])
        if final['proof_sha256'] != receipt['proof_sha256']:
            raise RuntimeError('final proof hash differs')
        if final['scope'] != receipt['scope'] or final['verdicts'] != receipt['stream']['verdicts'] or \
                final['states'] != solved['states'] or final['archive'] != compressed['archive'] or \
                final['plan_sha256'] != digest(root / 'plan.json'):
            raise RuntimeError('final campaign bindings differ')
        if final['phase_markers'] != {name: file_record(root / ('phase-' + name + '.json'))
                                     for name in ('solve', 'compress', 'verify')}:
            raise RuntimeError('final phase binding differs')
        print(json.dumps({'status': 'verified', 'idempotent': True, 'output': str(root)}))
        return 0
    attempts = root / 'attempts'
    attempts.mkdir(exist_ok=True)
    number = max([int(path.name) for path in attempts.iterdir() if path.is_dir()] + [0]) + 1
    attempt = attempts / f'{number:04d}'
    attempt.mkdir()
    record = {'status': 'running', 'attempt': number, 'started_at': datetime.now(timezone.utc).isoformat(),
              'n': plan['n'], 'plan_sha256': digest(root / 'plan.json'), 'phases': {}}
    save(attempt / 'started.json', record)
    started = time.monotonic()
    try:
        if solved is None:
            seconds = remaining_solver_seconds(root, plan)
            command = [str(build / 'solver'), '--n', str(plan['n']), '--trees', plan['trees'],
                       '--workers', str(plan['workers']),
                       '--top', '0:' + str(TREE_COUNTS[plan['n']]), '--states', str(root / 'packing.states'),
                       '--checkpoint', str(root / 'checkpoint.bin'), '--seconds', str(seconds),
                       '--memory-mib', str(plan['limits']['memory_mib']),
                       '--max-output-mib', str(plan['limits']['max_state_mib']),
                       '--checkpoint-seconds', str(plan['limits']['checkpoint_seconds']),
                       '--progress', str(attempt / 'progress.json')]
            if (root / 'checkpoint.bin').exists():
                record['resume_checkpoint'] = file_record(root / 'checkpoint.bin')
                command.append('--resume')
            result = phase(root, attempt, 'solve', command, seconds, plan, lock_descriptor)
            record['phases']['solve'] = result
            if result['exit_code'] == 3 or result['exit_code'] in (-signal.SIGTERM, -signal.SIGKILL, -signal.SIGINT):
                raise Incomplete('solver interrupted; restart requires its last committed checkpoint')
            if result['exit_code'] != 0:
                raise RuntimeError('solver failed')
            outcome = load(attempt / 'solve.out')
            expected = {'status': 'complete', 'n': plan['n'], 'top_first': 0,
                        'top_last': TREE_COUNTS[plan['n']], 'completed': TREE_COUNTS[plan['n']]}
            if any(outcome.get(key) != value for key, value in expected.items()):
                raise RuntimeError('solver did not complete full scope')
            states = state_metadata(root, plan, verifier)
            if outcome['nodes'] != states['nodes'] or outcome['states_bytes'] != states['bytes']:
                raise RuntimeError('solver state statistics differ')
            imported = plan.get('imported_checkpoint')
            if imported is not None:
                inspection = imported['inspection']
                if outcome.get('resumed') is not True or outcome.get('resumed_states', -1) < inspection['stored_states'] or \
                        outcome.get('resumed_completed', -1) < inspection['completed']:
                    raise RuntimeError('solver did not restore the imported checkpoint')
                if number == 1 and (outcome['resumed_states'] != inspection['stored_states'] or
                                    outcome['resumed_completed'] != inspection['completed']):
                    raise RuntimeError('first attempt did not use the exact imported checkpoint')
            artifacts = {'packing.states': {key: states[key] for key in ('bytes', 'sha256')},
                         'checkpoint.bin': file_record(root / 'checkpoint.bin')}
            for suffix in ('out', 'err', 'started.json', 'finished.json'):
                name = (attempt / ('solve.' + suffix)).relative_to(root).as_posix()
                artifacts[name] = file_record(root / name)
            solved = marker(root, 'solve', {'status': 'complete', 'states': states, 'outcome': outcome, 'artifacts': artifacts})
        states = solved['states']
        if compressed is None:
            temporary = attempt / 'packing.states.zst'
            result = phase(root, attempt, 'compress', [plan['compressor'], '-q', '-3', '-T1', '--check',
                                                      str(root / 'packing.states'), '-o', str(temporary)],
                           plan['limits']['verify_seconds'], plan, lock_descriptor)
            record['phases']['compress'] = result
            if result['exit_code'] != 0:
                raise RuntimeError('compression failed')
            archive = file_record(temporary, deadline)
            with temporary.open('rb') as stream:
                os.fsync(stream.fileno())
            destination = root / 'packing.states.zst'
            if destination.exists():
                if file_record(destination, deadline) != archive:
                    raise RuntimeError('uncommitted archive differs from recompression')
            else:
                os.link(temporary, destination)
                sync_directory(root)
            compressed = marker(root, 'compress', {'status': 'complete', 'archive': archive,
                                                   'artifacts': {'packing.states.zst': archive}})
        archive = compressed['archive']
        if verified is None:
            output = attempt / 'verification'
            command = [sys.executable, str(verifier_path), '--archive', str(root / 'packing.states.zst'),
                       '--streamer', str(build / 'compact_states'), '--checker', str(build / 'check_proof'),
                       '--independent-checker', str(build / 'check_proof_independent'), '--trees', plan['trees'],
                       '--n', str(plan['n']), '--top-first', '0', '--top-last', str(TREE_COUNTS[plan['n']]),
                       '--expected-archive-sha256', archive['sha256'], '--expected-states-sha256', states['sha256'],
                       '--expected-states-bytes', str(states['bytes']), '--output', str(output),
                       '--seconds', str(plan['limits']['verify_seconds']), '--memory-mib', str(plan['limits']['memory_mib']),
                       '--max-proof-mib', str(plan['limits']['max_proof_mib']), '--lock-fd', str(lock_descriptor)]
            result = phase(root, attempt, 'verify', command, plan['limits']['verify_seconds'], plan, lock_descriptor)
            record['phases']['verify'] = result
            if result['exit_code'] != 0:
                raise RuntimeError('dual verification failed')
            receipt = verification_receipt(root, plan, states, archive, output / 'finished.json')
            artifacts = {(path.relative_to(root)).as_posix(): file_record(path)
                         for path in output.iterdir() if path.is_file()}
            verified = marker(root, 'verify', {'status': 'verified', 'receipt': (output / 'finished.json').relative_to(root).as_posix(),
                                               'artifacts': artifacts})
        receipt = verification_receipt(root, plan, states, archive, root / verified['receipt'])
        verify_bindings(plan, deadline)
        for name in ('solve', 'compress', 'verify'):
            marker(root, name)
        final = {'status': 'verified', 'finished_at': datetime.now(timezone.utc).isoformat(),
                 'n': plan['n'], 'top_first': 0, 'top_last': TREE_COUNTS[plan['n']], 'roots': TREE_COUNTS[plan['n']],
                 'scope': receipt['scope'], 'states': states, 'archive': archive,
                 'states_bytes': states['bytes'], 'states_sha256': states['sha256'],
                 'archive_bytes': archive['bytes'], 'archive_sha256': archive['sha256'],
                 'proof_sha256': receipt['proof_sha256'], 'proof_bytes': receipt['proof_bytes'],
                 'verdicts': receipt['stream']['verdicts'], 'verification_receipt': verified['receipt'],
                 'verification_seconds': receipt['wall_seconds'], 'raw_proof_saved': False,
                 'plan_sha256': digest(root / 'plan.json'), 'attempts': number, 'n13_on_hold': plan['n13_on_hold'],
                 'workers': plan['workers'], 'inherited_solver_seconds': plan.get('inherited_solver_seconds', 0),
                 'imported_checkpoint': plan.get('imported_checkpoint'),
                 'phase_markers': {name: file_record(root / ('phase-' + name + '.json')) for name in ('solve', 'compress', 'verify')},
                 'input_bindings': plan['bindings'],
                 'phase_seconds': {path.parent.name + '/' + path.stem.removesuffix('.finished'): load(path)['wall_seconds']
                                   for path in attempts.glob('*/*.finished.json')}}
        save(root / 'finished.json', final)
        record['status'] = 'verified'
    except Exception as error:
        record.update(status='incomplete' if isinstance(error, Incomplete) else 'failed', error=str(error))
    record.update(finished_at=datetime.now(timezone.utc).isoformat(), wall_seconds=time.monotonic() - started)
    if (root / 'checkpoint.bin').exists():
        record['checkpoint'] = file_record(root / 'checkpoint.bin')
    save(attempt / 'finished.json', record)
    save(root / 'status.json', record, replace=True)
    print(json.dumps({'status': record['status'], 'attempt': number, 'error': record.get('error'), 'output': str(root)}))
    return 0 if record['status'] == 'verified' else 3 if record['status'] == 'incomplete' else 1


def prepare_campaign(args, root, parser):
    with ExitStack() as import_locks:
        if args.n == 13 and not args.allow_n13:
            parser.error('n13 remains on hold; explicit authorization is required')
        if args.aggregate_memory_mib is None:
            args.aggregate_memory_mib = 3 * args.memory_mib
        names = ('solver_seconds', 'verify_seconds', 'memory_mib', 'aggregate_memory_mib', 'max_state_mib', 'max_proof_mib',
                 'checkpoint_seconds', 'minimum_free_mib', 'maximum_disk_mib', 'total_seconds')
        limits = {name: getattr(args, name) for name in names}
        if min(limits.values()) <= 0:
            parser.error('limits must be positive')
        build, trees = args.build.resolve(strict=True), args.trees.resolve(strict=True)
        source, compressor, bindings = bind_inputs(build, trees)
        if bool(args.import_checkpoint) != bool(args.import_provenance):
            parser.error('checkpoint import requires both checkpoint and provenance')
        imported, original, inspection = None, None, None
        deadline = time.time() + args.total_seconds
        if args.import_checkpoint:
            checkpoint = args.import_checkpoint.resolve(strict=True)
            provenance_path = args.import_provenance.resolve(strict=True)
            imported, original = validate_import(checkpoint, provenance_path, build, args.n, args.solver_seconds, args.import_mode, import_locks)
            deadline = min(deadline, imported['accounting']['deadline_epoch'])
            import_plan = {'n': args.n, 'trees': str(trees)}
            inspection = inspect_checkpoint(build, checkpoint, import_plan, args.max_state_mib * 1024**2, deadline)
            if inspection != imported['inspection']:
                raise RuntimeError('import checkpoint inspection differs from export')
            for path in (checkpoint, provenance_path, provenance_path.parent / 'export.json'):
                bindings[str(path)] = file_record(path, deadline)
        root.mkdir(parents=True, exist_ok=False)
        plan = {'n': args.n, 'scope': {'n': args.n, 'top_first': 0, 'top_last': TREE_COUNTS[args.n]},
                'created_at': datetime.now(timezone.utc).isoformat(), 'deadline_epoch': deadline, 'workers': args.workers,
                'build': str(build), 'source': str(source), 'trees': str(trees), 'compressor': str(compressor),
                'bindings': bindings, 'limits': limits, 'n13_on_hold': not args.allow_n13,
                'restart': 'Committed memo checkpoint; completed phases reused only after hash checks.',
                'time_budget': 'Cumulative solver time across attempts; fixed campaign wall deadline includes downtime.',
                'memory_measurement': 'Process-tree RSS sampled every0.2s on Linux; shared pages counted perprocess.'}
        if imported is not None:
            plan['inherited_solver_seconds'] = imported['accounting']['solver_seconds_spent']
            plan['imported_checkpoint'] = {'checkpoint': str(checkpoint), 'provenance': str(provenance_path),
                                           'checkpoint_record': imported['checkpoint'], 'inspection': inspection,
                                           'origin': imported['origin'], 'origin_active': imported['origin_active'], 'mode': args.import_mode}
            copy_checkpoint(checkpoint, root / 'checkpoint.bin', args.max_state_mib * 1024**2,
                            deadline, imported['checkpoint'])
        save(root / 'plan.json', plan)
        save(root / 'campaign.json', {'plan_sha256': digest(root / 'plan.json'), 'n13_on_hold': plan['n13_on_hold']})
        return plan


def main():
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest='action', required=True)
    start = subparsers.add_parser('start')
    start.add_argument('--n', type=int, choices=range(2, 14), required=True)
    start.add_argument('--build', type=Path, required=True)
    start.add_argument('--trees', type=Path, required=True)
    start.add_argument('--output', type=Path, required=True)
    start.add_argument('--allow-n13', action='store_true')
    start.add_argument('--workers', type=int, choices=range(1, 33), default=1)
    start.add_argument('--import-checkpoint', type=Path)
    start.add_argument('--import-provenance', type=Path)
    start.add_argument('--import-mode', choices=('handoff', 'benchmark'), default='handoff')
    start.add_argument('--aggregate-memory-mib', type=int)
    for name, default in (('solver-seconds', 7200), ('verify-seconds', 7200), ('memory-mib', 8192),
                          ('max-state-mib', 4096), ('max-proof-mib', 32768), ('checkpoint-seconds', 30),
                          ('minimum-free-mib', 65536), ('maximum-disk-mib', 16384), ('total-seconds', 21600)):
        start.add_argument('--' + name, type=int, default=default)
    resume = subparsers.add_parser('resume')
    resume.add_argument('--output', type=Path, required=True)
    export = subparsers.add_parser('export-checkpoint')
    export.add_argument('--output', type=Path, required=True)
    export.add_argument('--build', type=Path, required=True)
    export.add_argument('--destination', type=Path, required=True)
    export.add_argument('--seconds', type=int, default=3600)
    args = parser.parse_args()
    signal.signal(signal.SIGINT, interrupt)
    signal.signal(signal.SIGTERM, interrupt)
    if args.output.is_symlink():
        parser.error('output must not be a symlink')
    if args.action == 'export-checkpoint':
        return export_checkpoint(args)
    root = args.output.resolve()
    if args.action == 'start':
        plan = prepare_campaign(args, root, parser)
    else:
        root = root.resolve(strict=True)
        plan = load(root / 'plan.json')
    if (root / 'campaign.lock').is_symlink():
        raise RuntimeError('campaign lock must not be a symlink')
    with (root / 'campaign.lock').open('a+b') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise RuntimeError('campaign or inherited child remains active') from error
        return execute(root, plan, lock.fileno())


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError, KeyError) as error:
        print(json.dumps({'status': 'failed', 'error': str(error)}), file=sys.stderr)
        raise SystemExit(1)

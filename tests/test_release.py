# release integration tests
# n9 campaign > completed resume; bounded checkpoint > resume > state proof > placement certificate
# both formats > restoration & two checkers; corrupt archive & proof > rejection
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time


ROOTS = 47


def digest(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        while block := stream.read(1024 * 1024):
            value.update(block)
    return value.hexdigest()


def load(path):
    return json.loads(path.read_text())


def interrupt(number, frame):
    raise KeyboardInterrupt


def run(name, command, output, records, expected=0, seconds=180, stdout_path=None):
    command = list(map(str, command))
    stdout_path = stdout_path or output / (name + '.out')
    stderr_path = output / (name + '.err')
    started = time.monotonic()
    with stdout_path.open('xb') as stdout, stderr_path.open('xb') as stderr:
        process = subprocess.Popen(command, stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr)
        try:
            code = process.wait(timeout=seconds)
        except BaseException:
            process.terminate()
            try:
                process.wait(timeout=90)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
            raise
    result = {'name': name, 'command': command, 'exit_code': code,
              'wall_seconds': time.monotonic() - started,
              'stdout': stdout_path.name, 'stdout_sha256': digest(stdout_path),
              'stderr': stderr_path.name, 'stderr_sha256': digest(stderr_path)}
    records.append(result)
    if code != expected:
        raise RuntimeError(name + ' returned ' + str(code) + '; see ' + str(stderr_path))
    print(json.dumps({'test': name, 'status': 'passed', 'seconds': result['wall_seconds']}), flush=True)
    return result


def verified(receipt):
    stream = receipt['stream']
    verdicts = stream['verdicts']
    expected = {'status': 'verified', 'n': 9, 'top_first': 0, 'top_last': ROOTS, 'roots': ROOTS}
    if receipt['status'] != 'verified' or set(verdicts) != {'checker', 'independent_checker'} or \
            verdicts['checker'] != verdicts['independent_checker']:
        raise RuntimeError('both matching checker verdicts required')
    verdict = verdicts['checker']
    if any(verdict.get(key) != value for key, value in expected.items()) or verdict['nodes'] <= 0:
        raise RuntimeError('full n9 scope required')
    if stream['producer_exit'] != 0 or stream['checker_exits'] != {'checker': 0, 'independent_checker': 0} or \
            stream['proof_bytes'] != verdict['proof_bytes'] or \
            stream['delivered_bytes'] != {name: verdict['proof_bytes'] for name in verdicts}:
        raise RuntimeError('complete proof delivery required')
    for name, expected_hash in receipt['logs_sha256'].items():
        if digest(Path(receipt['_directory']) / name) != expected_hash:
            raise RuntimeError('verification log changed: ' + name)
    return verdict


def receipt(path):
    value = load(path)
    value['_directory'] = str(path.parent)
    verified(value)
    return value


def main():
    parser = argparse.ArgumentParser(description='Small complete release workflows and corruption controls.')
    parser.add_argument('--build', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists() or args.output.is_symlink():
        parser.error('output must be a new directory')
    source = Path(__file__).resolve().parents[1]
    build = args.build.resolve(strict=True)
    output = args.output.resolve()
    compressor = shutil.which('zstd')
    if compressor is None:
        parser.error('zstd is required')
    campaign_build = build / 'campaign/bin'
    state_build = build / 'state-verification/bin'
    placement_build = build / 'placement-verification/bin'
    for directory, names in ((campaign_build, ('solver', 'compact_states', 'check_proof', 'check_proof_independent')),
                             (state_build, ('compact_states', 'check_proof', 'check_proof_independent')),
                             (placement_build, ('witness_codec', 'check_proof', 'check_proof_independent'))):
        for name in names:
            if not (directory / name).is_file():
                parser.error('missing build output: ' + str(directory / name))
    output.mkdir(parents=True, exist_ok=False)
    for number in (signal.SIGINT, signal.SIGTERM):
        signal.signal(number, interrupt)
    source_files = [source / 'trees.txt']
    for directory in ('solver', 'checkers', 'reconstruction'):
        source_files.extend(path for path in (source / directory).rglob('*')
                            if path.is_file() and '__pycache__' not in path.parts)
    sources = {path.relative_to(source).as_posix(): digest(path) for path in source_files}
    records = []
    summary = {'status': 'running', 'started_at': datetime.now(timezone.utc).isoformat(),
               'n': 9, 'source_sha256': sources, 'commands': records}
    began = time.monotonic()
    runner = source / 'solver/run_campaign.py'
    trees = source / 'trees.txt'
    campaign = output / 'campaign'
    try:
        run('campaign', [sys.executable, runner, 'start', '--n', '9', '--workers', '2',
                        '--build', campaign_build, '--trees', trees, '--output', campaign,
                        '--solver-seconds', '120', '--verify-seconds', '120', '--memory-mib', '1024',
                        '--aggregate-memory-mib', '3072', '--max-state-mib', '32', '--max-proof-mib', '32',
                        '--checkpoint-seconds', '1', '--minimum-free-mib', '64',
                        '--maximum-disk-mib', '256', '--total-seconds', '600'], output, records, seconds=300)
        completed = load(campaign / 'finished.json')
        campaign_receipt = receipt(campaign / completed['verification_receipt'])
        final_hash = digest(campaign / 'finished.json')
        attempts = sorted(path.name for path in (campaign / 'attempts').iterdir())
        run('completed-resume', [sys.executable, runner, 'resume', '--output', campaign], output, records)
        if final_hash != digest(campaign / 'finished.json') or attempts != sorted(path.name for path in (campaign / 'attempts').iterdir()):
            raise RuntimeError('completed resume changed the campaign')

        checkpoint = output / 'checkpoint.bin'
        states = output / 'resumed.states'
        solver = [campaign_build / 'solver', '--n', '9', '--trees', trees, '--top', '0:47',
                  '--workers', '2', '--states', states, '--checkpoint', checkpoint,
                  '--seconds', '120', '--memory-mib', '1024', '--max-output-mib', '32',
                  '--checkpoint-seconds', '1']
        run('checkpoint-stop', [*solver, '--stop-after-roots', '1'], output, records, expected=3)
        stopped = load(output / 'checkpoint-stop.out')
        if stopped['status'] != 'incomplete' or stopped['stop_reason'] != 'roots' or stopped['completed'] != 1 or states.exists():
            raise RuntimeError('bounded solver did not stop at one root')
        run('checkpoint-inspect', [campaign_build / 'solver', '--n', '9', '--trees', trees,
                                  '--top', '0:47', '--inspect-checkpoint', checkpoint,
                                  '--seconds', '120', '--memory-mib', '1024', '--max-output-mib', '32'], output, records)
        inspected = load(output / 'checkpoint-inspect.out')
        checkpoint_hash = digest(checkpoint)
        run('checkpoint-resume', [*solver, '--resume'], output, records)
        resumed = load(output / 'checkpoint-resume.out')
        if resumed['status'] != 'complete' or resumed['completed'] != ROOTS or resumed['resumed'] is not True or \
                resumed['resumed_completed'] != 1 or resumed['resumed_states'] != inspected['stored_states']:
            raise RuntimeError('checkpoint work was not restored')
        archive = output / 'resumed.states.zst'
        run('state-compress', [compressor, '-q', '-3', '-T1', '--check', states, '-o', archive], output, records)
        state_command = [sys.executable, source / 'reconstruction/verify_states.py',
                         '--archive', archive, '--streamer', state_build / 'compact_states',
                         '--checker', state_build / 'check_proof',
                         '--independent-checker', state_build / 'check_proof_independent',
                         '--trees', trees, '--n', '9', '--top-first', '0', '--top-last', str(ROOTS),
                         '--expected-archive-sha256', digest(archive), '--expected-states-sha256', digest(states),
                         '--expected-states-bytes', str(states.stat().st_size), '--seconds', '120',
                         '--memory-mib', '1024', '--max-proof-mib', '32', '--workers', '2']
        run('state-verification', [*state_command, '--output', output / 'state-verification',
                                  '--deadline-epoch', str(time.time() + 120)], output, records)
        state_receipt = receipt(output / 'state-verification/finished.json')
        if state_receipt['restore']['states_sha256'] != digest(states):
            raise RuntimeError('restored state certificate changed')

        proof = output / 'fixture.proof'
        run('state-stream', [state_build / 'compact_states', 'stream', states, '--workers', '2',
                             '--seconds', '120', '--memory-mib', '1024', '--max-output-mib', '32'],
            output, records, stdout_path=proof)
        if digest(proof) != state_receipt['proof_sha256']:
            raise RuntimeError('reconstructed proof changed')
        compact = output / 'fixture.placements'
        run('placement-encode', [placement_build / 'witness_codec', 'encode', proof, compact,
                                '--seconds', '120', '--max-output-mib', '32'], output, records)
        placement_archive = output / 'fixture.placements.zst'
        run('placement-compress', [compressor, '-q', '-3', '-T1', '--check', compact, '-o', placement_archive], output, records)
        verdict = state_receipt['stream']['verdicts']['checker']
        run('placement-verification', [sys.executable, source / 'reconstruction/verify_placements.py',
                                      '--archive', placement_archive, '--decoder', placement_build / 'witness_codec',
                                      '--checker', placement_build / 'check_proof',
                                      '--independent-checker', placement_build / 'check_proof_independent',
                                      '--expected-archive-sha256', digest(placement_archive),
                                      '--expected-compact-sha256', digest(compact),
                                      '--expected-compact-bytes', str(compact.stat().st_size),
                                      '--expected-proof-bytes', str(verdict['proof_bytes']),
                                      '--expected-nodes', str(verdict['nodes']),
                                      '--expected-placements', str(verdict['placements']),
                                      '--n', '9', '--seconds', '120', '--output', output / 'placement-verification'], output, records)
        placement_receipt = receipt(output / 'placement-verification/finished.json')
        if placement_receipt['stream']['verdicts'] != state_receipt['stream']['verdicts']:
            raise RuntimeError('certificate formats cover different scopes')

        corrupt = output / 'corrupt.states.zst'
        content = bytearray(archive.read_bytes())
        content[len(content) // 2] ^= 1
        corrupt.write_bytes(content)
        corrupt_command = state_command[:]
        corrupt_command[corrupt_command.index('--archive') + 1] = corrupt
        run('corrupt-state', [*corrupt_command, '--output', output / 'corrupt-state',
                              '--deadline-epoch', str(time.time() + 120)], output, records, expected=1)
        rejected = load(output / 'corrupt-state/finished.json')
        if rejected['status'] != 'failed' or rejected.get('stream') or 'archive SHA-256 differs' not in rejected['error']:
            raise RuntimeError('corrupt archive was not rejected before streaming')
        bad_proof = output / 'corrupt.proof'
        content = bytearray(proof.read_bytes())
        content[0] ^= 1
        bad_proof.write_bytes(content)
        for checker in ('check_proof', 'check_proof_independent'):
            run('corrupt-' + checker, [state_build / checker, bad_proof, '--seconds', '30', '--max-mib', '32'],
                output, records, expected=1)
        if any(digest(source / name) != expected_hash for name, expected_hash in sources.items()):
            raise RuntimeError('source changed during testing')
        summary.update(status='passed', checkpoint_sha256=checkpoint_hash,
                       checkpoint_restored_states=inspected['stored_states'],
                       verdicts={name: value['stream']['verdicts'] for name, value in
                                 (('campaign', campaign_receipt), ('states', state_receipt), ('placements', placement_receipt))},
                       proof_sha256={name: value['proof_sha256'] for name, value in
                                     (('campaign', campaign_receipt), ('states', state_receipt), ('placements', placement_receipt))})
    except BaseException as error:
        summary.update(status='failed', error=f'{type(error).__name__}: {error}')
        raise
    finally:
        summary.update(finished_at=datetime.now(timezone.utc).isoformat(), wall_seconds=time.monotonic() - began)
        (output / 'results.json').write_text(json.dumps(summary, indent=2) + '\n')


if __name__ == '__main__':
    main()

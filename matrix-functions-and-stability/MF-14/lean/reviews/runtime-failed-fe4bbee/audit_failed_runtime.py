"""Authenticate the two completed MF14 failures. No compiler or remote mutation."""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess

D = Path(__file__).resolve().parents[2]
E = D / 'verification/MF14-linux-20260919'
spec = json.loads((E / 'SPEC.json').read_text())
W = Path(spec['worktree'])
P, proof = spec['project'], spec['proof']
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
hash_bytes = lambda b: hashlib.sha256(b).hexdigest()
git_commands = []


def git(*args):
    argv = ['git', *args]
    r = subprocess.run(argv, cwd=W, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    git_commands.append({'argv': argv, 'cwd': str(W), 'exit_code': r.returncode,
                         'stdout_sha256': hash_bytes(r.stdout), 'stderr_sha256': hash_bytes(r.stderr)})
    assert r.returncode == 0, r.stderr.decode()
    return r.stdout


def blob(path):
    return git('show', f'{proof}:{path}')


assert spec['expected_conclusion'] == 'failure'
assert proof == 'fe4bbee26cc79f06587c803c5c902164c1e02e8e'
snapshot_path = D / 'final-review-packets/MF14-v1/REVIEW-SNAPSHOT.json'
snapshot = json.loads(snapshot_path.read_text())
assert sha(snapshot_path) == 'e52fab5a7b58c3bc6fb2c2df1283d55c6e4352056689c900de936c12e2595436'
tree = git('rev-parse', f'{proof}^{{tree}}').decode().strip()
project_paths = git('ls-tree', '-r', '--name-only', proof, '--', P).decode().splitlines()
inputs = {str(Path(p).relative_to(P)): hash_bytes(blob(p)) for p in project_paths}
for path, digest in snapshot['Lean_sources'].items():
    assert inputs[path] == digest, path
assert len(snapshot['Lean_sources']) == 87
assert not git('diff', '--name-only', spec['base'], proof, '--', 'tools/lean', 'docs/lean',
               '.github/workflows/lean-verification.yml').strip()
config = json.loads(blob(f'{P}/comparator.json'))
names = config['theorem_names']
assert len(names) == len(set(names)) == 25
assert config['definition_names'] == []
assert config['challenge_module'] == 'Challenge' and config['solution_module'] == 'Solution'
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert set(config['permitted_axioms']) == allowed
manifest = json.loads(blob(f'{P}/lake-manifest.json'))
lock_bytes = blob('tools/lean/source-lock.json')
lock = json.loads(lock_bytes)
assert len(lock['files']) == 58
assert lock['commit'] == '8d1b0c0545a77b40245e84705aa7d273e6c81e62'
assert blob(f'{P}/lean-toolchain').decode().strip() == 'leanprover/lean4:v4.33.1'

# Preserve actual proof-commit source, not the mutable publication worktree.
reviewed_paths = ['.github/workflows/lean-verification.yml', 'tools/lean/harness.py',
                  'tools/lean/source-lock.json', 'tools/lean/verify.sh',
                  f'{P}/comparator.json', f'{P}/lakefile.toml', f'{P}/lake-manifest.json',
                  f'{P}/lean-toolchain', f'{P}/Challenge.lean', f'{P}/Solution.lean',
                  f'{P}/NLA/MF14Degree44/Mod3Certificate.lean']
for p in reviewed_paths:
    out = E / 'reviewed-proof-inputs' / p
    out.parent.mkdir(parents=True, exist_ok=True)
    data = blob(p)
    if out.exists():
        assert out.read_bytes() == data
    else:
        out.write_bytes(data)
(E / 'PROOF-INPUT-HASHES.json').write_text(json.dumps(inputs, indent=2) + '\n')

archive = D / 'publication/PF03/docs/lean/verification/2026-09-12/source/forsythe'
locked_sources = {}
for entry in lock['files']:
    if entry['destination'] not in {
        'scripts/strict_landrun.py', 'reproduction/checks/PinnedReplayProbe.lean',
        'reproduction/checks/run_replay.sh', 'reproduction/checks/sandbox_probe.py',
        'reproduction/checks/comparator_regressions.py'}:
        continue
    p = archive / entry['destination']
    assert p.stat().st_size == entry['bytes'] and sha(p) == entry['sha256']
    locked_sources[str(p)] = sha(p)

source_reference = blob(f'{P}/Challenge.lean').decode()
source_implementation = blob(f'{P}/NLA/MF14Degree44/Mod3Certificate.lean').decode()
pat = r'theorem integer_jacobian_mod3_inverse\s*:(.*?) := by'
headers = [re.search(pat, s, flags=re.S).group(1).strip()
           for s in [source_reference, source_implementation]]
assert headers[0] == headers[1]

records = []
for entry in spec['runs']:
    root = E / entry['kind']
    api = json.loads((root / 'GITHUB-PROVENANCE.json').read_text())
    run = api['run']
    assert run['id'] == entry['run_id'] and run['head_sha'] == proof
    assert api['repository'] == run['repository']['full_name'] == entry['repository']
    assert run['head_repository']['full_name'] == 'sgstepaniants/OpenProblemsInNLA'
    assert run['event'] == ('push' if entry['kind'] == 'fork' else 'pull_request')
    assert run['path'] == '.github/workflows/lean-verification.yml'
    assert run['status'] == 'completed' and run['conclusion'] == 'failure'
    assert len(api['jobs']['jobs']) == api['jobs']['total_count'] == 3
    selected = [j for j in api['jobs']['jobs'] if j['name'].startswith('verify (')]
    assert len(selected) == 1
    job = selected[0]
    assert job['name'] == f'verify (MF-14, {P})'
    assert job['status'] == 'completed' and job['conclusion'] == 'failure'
    step = next(s for s in job['steps'] if s['name'] == 'Fresh sandboxed statement, axiom and kernel verification')
    assert step['conclusion'] == 'failure' and step['number'] == 7
    assert next(j for j in api['jobs']['jobs'] if j['name'] == 'checker-controls')['conclusion'] == 'skipped'
    checked = api['checked_commit']
    assert checked['tree']['sha'] == tree, 'Checked merge has the exact full proof tree'
    if entry['kind'] == 'fork':
        assert checked['sha'] == proof
    else:
        assert [p['sha'] for p in checked['parents']] == [spec['base'], proof]
    assert api['artifacts']['total_count'] == len(api['artifacts']['artifacts']) == 1
    artifact = api['artifacts']['artifacts'][0]
    assert artifact['name'] == 'lean-MF-14' and not artifact['expired']
    assert artifact['workflow_run']['id'] == run['id']
    zip_path = root / 'lean-MF-14.zip'
    assert artifact['digest'] == 'sha256:' + sha(zip_path)
    assert artifact['size_in_bytes'] == zip_path.stat().st_size
    inventory = json.loads((root / 'ARTIFACT-FILES.json').read_text())
    assert len(inventory) == 12
    for f in inventory:
        p = root / 'artifact' / f['path']
        assert p.stat().st_size == f['bytes'] and sha(p) == f['sha256']
    assert not list((root / 'artifact').rglob('result.json'))
    comparator_paths = list((root / 'artifact').rglob('comparator.log'))
    assert len(comparator_paths) == 1
    logs = comparator_paths[0].parent
    expected = {
        'user-service.log': (0, ['systemd-run', '--user']),
        'dependencies.log': (0, []), 'mathlib-cache.log': (0, []),
        'sandbox.log': (0, ['Outer and export fixture contents unchanged; only designated build fixture written.']),
        'kernel-controls.log': (0, ['PASS: all three actual Comparator.runBuiltinKernel cases behaved as required']),
        'comparator-controls.log': (0, ['PASS: all five Comparator regressions']),
        'negative-sorry.log': (1, ["Illegal axiom detected: 'sorryAx'"]),
        'negative-native.log': (1, ["Illegal axiom detected: 'checked._native.native_decide.ax_1_1'"]),
        'comparator.log': (1, ['Building Challenge', 'Building Solution',
                            'Build completed successfully (2138 jobs).',
                            'Build completed successfully (3723 jobs).',
                            "uncaught exception: Challenge and solution theorem statement do not match: 'NLA.MF14Degree44.integer_jacobian_mod3_inverse'"]),
    }
    statuses = {}
    for name, (code, markers) in expected.items():
        p = logs / name
        s = p.read_text()
        assert s.rstrip().endswith(f'EXIT_STATUS={code}')
        assert all(m in s for m in markers), name
        statuses[name] = {'exit_status': code, 'sha256': sha(p), 'command': s.splitlines()[0]}
    dependency_text = (logs / 'dependencies.log').read_text()
    for package in manifest['packages']:
        assert f"info: {package['name']}: checking out revision '{package['rev']}'" in dependency_text
    sandbox = (logs / 'sandbox.log').read_text()
    assert sandbox.count('Sandbox UID: 1001') == 2
    for marker in ['PASS outside .lake write-open: denied', 'PASS outside .lake truncate: denied',
                   'PASS outside .lake read-only truncate-open: denied', 'PASS symlink from .lake to outside write: denied',
                   'PASS outside .lake creation: denied', 'PASS user namespace: private', 'PASS pid namespace: private',
                   'PASS mnt namespace: private', 'PASS net namespace: private', 'PASS ipc namespace: private',
                   'PASS uts namespace: private', 'PASS host parent: absent from private /proc',
                   'PASS host parent signal lookup: denied', 'PASS host loopback listener: unreachable',
                   'PASS AF_UNIX socket creation: denied', 'PASS effective capabilities: none',
                   'PASS no_new_privs: set', 'PASS nested namespace write attempt: rejected exit=1']:
        assert sandbox.count(marker) == 2, marker
    for marker in ['PASS build .lake write: allowed', 'PASS export .lake write-open: denied',
                   'PASS export .lake truncate: denied', 'NEGATIVE unknown option: exit=2',
                   'NEGATIVE unexpected --rw: exit=2', 'NEGATIVE unexpected --rwx: exit=2',
                   'NEGATIVE relative --rwx: exit=2']:
        assert sandbox.count(marker) == 1, marker
    kernel = (logs / 'kernel-controls.log').read_text()
    for marker in ['RETURN honest_with_inductives_and_quotients: accepted',
                   "RETURN invalid_raw_proof: rejected: while replaying declaration 'PinnedReplayProbe.invalid'",
                   "(kernel) declaration type mismatch, 'PinnedReplayProbe.invalid' has type",
                   'RETURN quotient_postcheck_mismatch: rejected: Quotient constant mismatch on: Quot.lift']:
        assert marker in kernel
    regression = (logs / 'comparator-controls.log').read_text()
    for case, status in [('simple_match', 0), ('simple_mismatch', 1), ('simple_axiom_issue', 1),
                         ('simple_kind_mismatch', 1), ('type_mismatch', 1)]:
        assert f'PASS {case}: exit {status}, expected {status}; required phase:' in regression
    comparator = comparator_paths[0].read_text()
    assert 'Running Lean default kernel on solution.' not in comparator
    assert 'Lean default kernel accepts the solution' not in comparator
    assert 'Your solution is okay!' not in comparator
    exports = re.findall(r'Exporting #\[(.*?)\] from (Challenge|Solution)', comparator)
    assert len(exports) == 2 and {m for _, m in exports} == {'Challenge', 'Solution'}
    for listing, module in exports:
        assert set(names) <= {n.strip() for n in listing.split(',')}
    reports = dict(re.findall(r"info: Solution\.lean:\d+:\d+: '([^']+)' depends on axioms: \[([^\]]*)\]", comparator))
    assert set(reports) == set(names)
    assert all({a.strip() for a in v.split(',')} <= allowed for v in reports.values())
    select = next(j for j in api['jobs']['jobs'] if j['name'] == 'select')
    assert select['conclusion'] == 'success'
    selection_log = (root / f"official-job-{select['id']}.raw.log").read_text()
    assert '{"include":[{"id":"MF-14","project":"matrix-functions-and-stability/MF-14/lean"}]}' in selection_log
    job_log = (root / f"official-job-{job['id']}.raw.log").read_text()
    assert checked['sha'] in job_log
    assert 'Process completed with exit code 2.' in job_log
    assert 'lean-MF-14.zip successfully finalized.' in job_log
    assert 'Lean (version 4.33.1, x86_64-unknown-linux-gnu' in job_log
    assert 'go version go1.27.1 linux/amd64' in job_log
    assert 'Image: ubuntu-24.04' in job_log and '24.04.5' in job_log
    records.append({'kind': entry['kind'], 'repository': entry['repository'], 'run_id': run['id'],
                    'run_url': run['html_url'], 'verify_job_id': job['id'], 'select_job_id': select['id'],
                    'official_conclusion': 'failure', 'failing_step': step,
                    'checked_commit': checked['sha'], 'checked_tree_equals_proof_tree': True,
                    'artifact_id': artifact['id'], 'artifact_digest': artifact['digest'],
                    'artifact_bytes': artifact['size_in_bytes'], 'artifact_files': len(inventory),
                    'verify_log_sha256': sha(root / f"official-job-{job['id']}.raw.log"),
                    'provenance_sha256': sha(root / 'GITHUB-PROVENANCE.json'),
                    'logs': statuses, 'actual_solution_axiom_reports': reports,
                    'all_25_contracts_exported_from_both_modules': True,
                    'all_25_statements_accepted': False,
                    'actual_solution_default_kernel_replay_reached': False,
                    'success_receipt_present': False, 'sandbox_uids': [1001, 1001],
                    'pinned_dependency_checkouts_matched': len(manifest['packages'])})

(E / 'AUDIT-GIT-COMMANDS.json').write_text(json.dumps(git_commands, indent=2) + '\n')
output = {'reviewer': spec['reviewer'], 'phase': 'independent nonauthor runtime evidence review',
          'scope': 'Authenticate actual official failed runs; no local Lean/Lake/Comparator execution',
          'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'verdict': 'BLOCKING: OFFICIAL COMPARATOR STATEMENT MISMATCH',
          'proof_commit': proof, 'base_commit': spec['base'], 'project': P,
          'script_sha256': sha(Path(__file__)), 'spec_sha256': sha(E / 'SPEC.json'),
          'proof_tree': tree, 'proof_project_input_count': len(inputs),
          'proof_input_hashes_sha256': sha(E / 'PROOF-INPUT-HASHES.json'),
          'frozen_Lean_sources_match_proof_commit': 87,
          'snapshot_sha256': sha(snapshot_path), 'source_lock_sha256': hash_bytes(lock_bytes),
          'archived_locked_verifier_sources': locked_sources,
          'mismatched_contract': 'NLA.MF14Degree44.integer_jacobian_mod3_inverse',
          'literal_source_headers_equal': True, 'literal_source_header': headers[0],
          'elaborated_type_cause': 'Not determined by this nonauthor runtime audit; coordinator local diagnosis is separate.',
          'runs': records, 'compiler_or_comparator_run_by_reviewer': False,
          'proof_workflow_publication_changes_by_reviewer': False, 'count_increment': 0,
          'limits': ['No result.json or bootstrap receipt is included in either failed artifact.',
                     'Per-input and tool-executable runtime hash maps cannot be compared because no success receipt was emitted.',
                     'Input binding rests on authenticated checkout/tree and the unchanged source-only snapshot harness.',
                     'Controls succeeding does not establish acceptance of this proof.',
                     'No new head, repair, or rerun is covered by this report.']}
(E / 'INDEPENDENT-AUDIT.json').write_text(json.dumps(output, indent=2) + '\n')
print(json.dumps({'verdict': output['verdict'], 'runs': len(records),
                  'proof_project_inputs': len(inputs), 'frozen_Lean_sources': 87,
                  'audit_sha256': sha(E / 'INDEPENDENT-AUDIT.json')}, indent=2))

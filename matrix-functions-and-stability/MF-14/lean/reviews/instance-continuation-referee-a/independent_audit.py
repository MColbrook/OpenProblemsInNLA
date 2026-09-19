"""Read-only source/log authentication; does not invoke Lean or Comparator."""
from pathlib import Path
from hashlib import sha256
import datetime
import difflib
import gzip
import json
import re

D = Path('/Users/georgestepaniants/Research/OpenProblemsInNLA/.local-recovery-20260918')
OUT = Path(__file__).parent
V1 = D / 'final-review-packets/MF14-v1'
V2 = D / 'final-review-packets/MF14-v2-instance-alignment'
AUD = D / 'verification/MF14-repair095-local-20260919'
digest = lambda b: sha256(b).hexdigest()
hash_file = lambda p: digest(p.read_bytes())
snap1 = json.loads((V1 / 'REVIEW-SNAPSHOT.json').read_text())
snap2 = json.loads((V2 / 'REVIEW-SNAPSHOT.json').read_text())
for base, snap in [(V1, snap1), (V2, snap2)]:
    for rel, expected in snap['files'].items():
        assert hash_file(base / rel) == expected, (base, rel)
assert snap1['Lean_sources'].keys() == snap2['Lean_sources'].keys()
changed = [p for p in snap1['Lean_sources'] if (V1 / p).read_bytes() != (V2 / p).read_bytes()]
assert changed == ['NLA/MF14Degree44/Mod3Certificate.lean']
rel = changed[0]
old, new = (V1 / rel).read_text(), (V2 / rel).read_text()
patch = ('-- Keep this public contract on the frozen commutative-ring instance.\n'
         '-- Imports below the proof route also expose a field instance for ZMod 3.\n'
         'attribute [-instance] ZMod.instField in\n')
assert old.replace('theorem integer_jacobian_mod3_inverse :',
                   patch + 'theorem integer_jacobian_mod3_inverse :', 1) == new
assert hash_file(D / 'development/MF14-instance-alignment-095' / rel) == hash_file(V2 / rel)
audit = json.loads((AUD / 'LOCAL-REPLAY-AUDIT.json').read_text())
receipts = {}
for run, item in audit['lossless_original_receipts'].items():
    raw_gz = (AUD / item['file']).read_bytes()
    assert digest(raw_gz) == item['gzip_sha256'], run
    raw = gzip.decompress(raw_gz)
    assert digest(raw) == item['original_sha256'], run
    receipts[run] = json.loads(raw)
records = {r['module']: r for r in audit['module_records']}
assert len(records) == 86
chain_links = 0
fresh_summary = []
for module, record in records.items():
    assert hash_file(V2 / record['source']) == record['source_sha256'], module
    for link in record['reuse_chain']:
        current = next(c for c in receipts[link['run']]['commands'] if c['module'] == module)
        assert current['status'] == 'reused_exact_successful_local_output', module
        assert current['source_sha256'] == record['source_sha256'], module
        assert current['output_sha256'] == record['output_sha256'], module
        assert current['prior_receipt_sha256'] == link['prior_receipt_sha256'], module
        assert audit['lossless_original_receipts'][link['prior']]['original_sha256'] == link['prior_receipt_sha256']
        assert Path(current['prior_receipt']).parent.name == link['prior'], module
        for path, source_hash in current['transitive_source_hashes'].items():
            assert snap2['Lean_sources'][path] == source_hash, (module, path)
        chain_links += 1
    command = record['actual_fresh_command']
    retained = next(c for c in receipts[record['fresh_success_run']]['commands'] if c['module'] == module)
    assert command == retained, module
    assert command['exit_code'] == 0, module
    assert command['source_sha256'] == record['source_sha256'], module
    assert command['output_sha256'] == record['output_sha256'], module
    assert '--threads=1' in command['argv'] and '--memory=4096' in command['argv'], module
    assert hash_file(AUD / record['log']) == command['log_sha256'], module
    for dep, output_hash in command['dependency_olean_sha256'].items():
        assert records[dep]['output_sha256'] == output_hash, (module, dep)
    if record['fresh_success_run'] == 'recovery-095':
        fresh_summary.append({k: command[k] for k in ['module', 'source_sha256', 'exit_code',
                              'elapsed_seconds', 'log_sha256', 'output_sha256']})
raw_ref = D / 'local-lean/runs/recovery-094/MF14ChallengeTypes093.log'
raw_sol = D / 'local-lean/runs/recovery-095/MF14SolutionTypes093.log'
assert raw_ref.read_bytes() == raw_sol.read_bytes()
contracts = snap2['contracts']
dump = raw_ref.read_text()
assert re.findall(r'^TYPEJSON (\S+) ', dump, re.M) == contracts
assert re.findall(r'^LEVELJSON (\S+) ', dump, re.M) == contracts
for run, name in [('recovery-094', 'MF14ChallengeTypes093'), ('recovery-095', 'MF14SolutionTypes093')]:
    rpath = D / f'local-lean/runs/{run}/RECEIPT.json'
    receipt = json.loads(rpath.read_text())
    command = next(c for c in receipt['commands'] if c['module'] == name)
    source = D / 'local-lean' / (name + '.lean')
    assert hash_file(source) == command['source_sha256']
    assert command['exit_code'] == 0
    assert hash_file(D / f'local-lean/runs/{run}/{name}.log') == command['log_sha256']
    code = source.read_text()
    assert re.findall(r'let info ← getConstInfo `(\S+)', code) == contracts
    assert len(re.findall(r'\+\+ reprStr info.type\)', code)) == 25
    assert len(re.findall(r'\+\+ reprStr info.levelParams\)', code)) == 25
sol_log = (D / 'local-lean/runs/recovery-095/Solution.log').read_text()
axioms = dict(re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", sol_log))
assert list(axioms) == contracts
assert all(set(a.split(', ')) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in axioms.values())
assert (V2 / 'Solution.lean').read_text().count('#assert_trust kernel') == 25
noholes = []
for path in snap2['Lean_sources']:
    if path == 'Challenge.lean':
        continue
    code = (V2 / path).read_text()
    code = re.sub(r'/\-.*?\-/', '', code, flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    assert not re.search(r'\b(?:sorry|admit|native_decide|sorryAx)\b|^\s*axiom\b', code, re.M), path
    noholes.append(path)
linux = []
for org in ['fork', 'upstream']:
    base = D / 'verification/MF14-linux-20260919' / org
    runpath = base / 'official-run.json'
    run = json.loads(runpath.read_text())
    log = next((base / 'artifact').glob('verify*/comparator.log'))
    text = log.read_text()
    assert 'Build completed successfully' in text
    assert "Challenge and solution theorem statement do not match: 'NLA.MF14Degree44.integer_jacobian_mod3_inverse'" in text
    assert text.rstrip().endswith('EXIT_STATUS=1')
    linux.append({'run_id': run['id'], 'url': run['html_url'], 'head_sha': run['head_sha'],
                  'conclusion': run['conclusion'], 'run_metadata_sha256': hash_file(runpath),
                  'comparator_log_sha256': hash_file(log)})
result = {
    'reviewer': '/root/nr04_mf14_final_referee_a',
    'timestamp_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'scope': 'Static source, receipt and log authentication only; no Lean/Comparator invocation',
    'v1_snapshot_sha256': hash_file(V1 / 'REVIEW-SNAPSHOT.json'),
    'v2_snapshot_sha256': hash_file(V2 / 'REVIEW-SNAPSHOT.json'),
    'registered_file_hash_checks_each_snapshot': len(snap2['files']),
    'Lean_files_compared': len(snap2['Lean_sources']),
    'changed_Lean_files': changed,
    'exact_three_line_addition_verified': True,
    'changed_source_sha256': hash_file(V2 / rel),
    'replay_audit_sha256': hash_file(AUD / 'LOCAL-REPLAY-AUDIT.json'),
    'authenticated_gzip_receipts': len(receipts),
    'authenticated_module_origins': len(records),
    'authenticated_reuse_links': chain_links,
    'fresh095_proof_commands': fresh_summary,
    'raw_type_and_universe_dumps_equal': True,
    'raw_dump_bytes': raw_ref.stat().st_size,
    'raw_dump_sha256': hash_file(raw_ref),
    'contract_count': len(contracts),
    'permitted_axioms_only': True,
    'kernel_assertion_count': 25,
    'proof_sources_scanned_for_holes': len(noholes),
    'original_failed_Linux_runs_inspected': linux,
    'repaired_Linux_run_inspected': False,
    'reviewer_Lean_run': False,
    'reviewer_Comparator_run': False,
    'count_increment': 0,
}
(OUT / 'INDEPENDENT-AUDIT.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k not in ['fresh095_proof_commands', 'original_failed_Linux_runs_inspected']}, indent=2))

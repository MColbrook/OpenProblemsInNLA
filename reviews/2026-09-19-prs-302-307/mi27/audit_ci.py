from pathlib import Path
import hashlib, json, re
OUT = Path('/tmp/pr-audit-20260919/agent-mi27')
ROOT = OUT / 'worktree'
P = ROOT / 'matrix-inequalities-and-norms/MI-27/lean'
CI = Path('/tmp/pr-audit-20260919/ci/mi27/verify-20260919T104455Z-4157')
sha = lambda b: hashlib.sha256(b).hexdigest()
r = json.loads((CI / 'result.json').read_text())
cfg = json.loads((P / 'comparator.json').read_text())
assert r['config'] == cfg
assert r['result'] == 'comparator-accepted'
assert r['project'] == str(P.relative_to(ROOT))
assert r['source_lock_sha256'] == sha((ROOT / 'tools/lean/source-lock.json').read_bytes())
for rel, expected in r['input_sha256'].items():
    assert sha((P / rel).read_bytes()) == expected, rel
actual = {str(f.relative_to(P)) for f in P.rglob('*') if f.is_file()}
assert actual == set(r['input_sha256'])
assert r['tool_receipt']['lean_toolchain'] == (P / 'lean-toolchain').read_text().strip()
assert r['tool_receipt']['platform'].startswith('Linux-')
logs = {f.name: f.read_text() for f in CI.glob('*.log')}
checks = {
    'comparator.log': ['Lean default kernel accepts the solution', 'Your solution is okay!', 'EXIT_STATUS=0'],
    'comparator-controls.log': ['PASS: all five Comparator regressions', 'EXIT_STATUS=0'],
    'kernel-controls.log': ['PASS: all three actual Comparator.runBuiltinKernel cases behaved as required', 'invalid_raw_proof: rejected', 'quotient_postcheck_mismatch: rejected', 'EXIT_STATUS=0'],
    'sandbox.log': ['MODE build: exit=0', 'MODE export: exit=0', 'Sandbox UID: 1001', 'PASS AF_UNIX socket creation: denied', 'PASS host loopback listener: unreachable', 'PASS nested namespace write attempt: rejected', 'Outer and export fixture contents unchanged', 'EXIT_STATUS=0'],
    'negative-sorry.log': ["Illegal axiom detected: 'sorryAx'", 'EXIT_STATUS=1'],
    'negative-native.log': ["Illegal axiom detected: 'checked._native.native_decide.ax_1_1'", 'EXIT_STATUS=1'],
}
for f, phrases in checks.items():
    for phrase in phrases: assert phrase in logs[f], (f, phrase)
axioms = {m[1]: [x.strip() for x in m[2].split(',')] for m in re.finditer(r"info: Solution.lean:\d+:\d+: '([^']+)' depends on axioms: \[([^\]]*)\]", logs['comparator.log'])}
assert set(axioms) == set(cfg['theorem_names'])
assert all(set(a) == {'propext','Classical.choice','Quot.sound'} for a in axioms.values())
result = {'verdict':'PASS_EXTERNAL_CI_SOURCE_AND_CONTROL_AUDIT','head':'1f05b398013d44beb7d756cbfbbfd3e875c8deab','run_id':35438172834,'artifact_id':10583511156,'artifact_archive_sha256_from_root':'50394e222707d250e7e1fc58dc80b8f6e59fb475b324a3414fd59f36e045b094','ci_repository_commit':r['repository_commit'],'matched_project_inputs':len(r['input_sha256']),'all_inputs_matched':True,'matched_theorems':len(axioms),'controls':list(checks),'log_sha256':{f:sha((CI/f).read_bytes()) for f in checks},'semantic_review':'Separate source review in REPORT.md; CI does not perform semantic review.'}
(OUT/'ci-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

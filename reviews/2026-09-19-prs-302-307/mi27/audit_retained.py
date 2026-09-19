from pathlib import Path
import datetime, gzip, hashlib, json, re, subprocess

ROOT = Path('/tmp/pr-audit-20260919/agent-mi27/worktree')
P = ROOT / 'matrix-inequalities-and-norms/MI-27/lean'
OUT = ROOT.parent
E = P / 'verification/local-2026-09-19'
T = P / 'verification/type-preflight-118'
sha = lambda b: hashlib.sha256(b).hexdigest()
read = lambda p: json.loads(p.read_text())

def check(p, expected):
    assert sha(p.read_bytes()) == expected, str(p)

def no_comments(s):
    out, depth, i = [], 0, 0
    while i < len(s):
        if s.startswith('/-', i):
            depth += 1; i += 2
        elif depth and s.startswith('-/', i):
            depth -= 1; i += 2
        elif depth:
            if s[i] == '\n': out.append('\n')
            i += 1
        elif s.startswith('--', i):
            end = s.find('\n', i); i = len(s) if end < 0 else end
        else:
            out.append(s[i]); i += 1
    assert depth == 0
    return ''.join(out)

snapshot = read(P / 'REVIEW-SNAPSHOT.json')
pre = read(P / 'verification/PUBLICATION-PREFLIGHT.json')
check(P / 'REVIEW-SNAPSHOT.json', pre['source_snapshot_sha256'])
cfg, freeze = read(P / 'comparator.json'), read(P / 'STATEMENT-FREEZE.json')
names = cfg['theorem_names']
assert len(names) == len(set(names)) == 20
assert names == freeze['contract_names']
assert cfg['definition_names'] == []
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert set(cfg['permitted_axioms']) == allowed
for rel, h in freeze['frozen_files'].items(): check(P / rel, h)
for rel, h in pre['Lean_sources'].items():
    check(P / rel, h)
    assert snapshot['files'][rel] == h
proof = {str(p.relative_to(P))[:-5].replace('/', '.'): str(p.relative_to(P))
         for p in (P / 'NLA').rglob('*.lean')}
proof['Solution'] = 'Solution.lean'
assert len(proof) == 52
imports, headers = {}, {}
for mod, rel in proof.items():
    src = no_comments((P / rel).read_text())
    check(P / rel, snapshot['files'][rel])
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|ofReduceBool|skipKernelTC)\b|^\s*(opaque|run_cmd|elab|macro|initialize)\b', src, re.M), rel
    deps = [w for line in src.splitlines() if line.startswith('import ') for w in line[7:].split()]
    imports[mod] = [d for d in deps if not d.startswith(('Mathlib.', 'LeanCert.'))]
    assert all(d in proof for d in imports[mod]), (rel, imports[mod])
    for m in re.finditer(r'^theorem\s+(\w+)(.*?)\s*:=\s*by', src, re.M | re.S):
        full = 'NLA.MI27.' + m[1]
        if full in names:
            assert full not in headers
            headers[full] = re.sub(r'\s+', ' ', m[2]).strip()
challenge = no_comments((P / 'Challenge.lean').read_text())
assert len(re.findall(r'\bsorry\b', challenge)) == 20
for m in re.finditer(r'^theorem\s+(\w+)(.*?)\s*:=\s*by', challenge, re.M | re.S):
    assert headers['NLA.MI27.' + m[1]] == re.sub(r'\s+', ' ', m[2]).strip()
assert set(headers) == set(names)
closures = {}
def closure(mod, active=()):
    assert mod not in active
    if mod not in closures:
        c = {mod}
        for d in imports[mod]: c |= closure(d, active + (mod,))
        closures[mod] = c
    return closures[mod]
assert closure('Solution') == set(proof)
for p in (P / 'NLA/MI24').glob('*.lean'):
    basepath = 'matrix-inequalities-and-norms/MI-24/lean/NLA/MI24/' + p.name
    old = subprocess.check_output(['git', 'show', snapshot['canonical_base'] + ':' + basepath], cwd=ROOT)
    assert old == p.read_bytes(), p.name
lock = read(P / 'lake-manifest.json')
pins = {p['name']: p['rev'] for p in lock['packages']}
assert len(pins) == 10 and all(re.fullmatch('[0-9a-f]{40}', r) for r in pins.values())
assert lock['name'] == 'NLAMI27'
assert (P / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.1'
env = read(E / 'LOCAL-ENVIRONMENT.json')
assert all(pins[p['name']] == p['commit'] and p['tracked_source_clean'] for p in env['packages'])
audit = read(E / 'LOCAL-REPLAY-AUDIT.json')
check(E / 'LOCAL-REPLAY-AUDIT.json', pre['local_audit_sha256'])
check(E / 'serial_compile_recovery.py', audit['runner_sha256'])
receipts, receipt_hashes, commands = {}, {}, {}
for run, rec in audit['lossless_original_receipts'].items():
    blob = (E / rec['file']).read_bytes()
    assert sha(blob) == rec['gzip_sha256']
    raw = gzip.decompress(blob)
    assert sha(raw) == rec['original_sha256']
    rr = json.loads(raw)
    receipts[run], receipt_hashes[run] = rr, sha(raw)
    assert rr['compiler_sha256'] == env['compiler_sha256'] == audit['compiler_sha256']
    assert rr['platform'] == 'darwin' and rr['threads'] == 1 and rr['memory_cap_mib'] == 4096
    assert rr['max_compiler_processes'] == 1
    commands[run] = {c['module']: c for c in rr['commands']}
    assert len(commands[run]) == len(rr['commands'])
last = receipts['recovery-118']
assert receipt_hashes['recovery-118'] == audit['aggregate_receipt_sha256']
assert last['completed_modules'] == 55 and not last['failed_modules'] and not last['blocked_modules']
records = {r['module']: r for r in audit['module_records']}
assert set(records) == set(proof)
reuse_edges, intervals = 0, []
for mod, rel in proof.items():
    rec = records[mod]
    assert rec['source'] == rel and rec['source_sha256'] == snapshot['files'][rel]
    run, seen, chain = 'recovery-118', set(), []
    while True:
        assert run not in seen
        seen.add(run)
        rr, cmd = receipts[run], commands[run][mod]
        for d in closure(mod):
            r = rr['source_inputs'][proof[d]]
            h = r['sha256'] if isinstance(r, dict) else r
            assert h == snapshot['files'][proof[d]], (run, mod, d)
        assert cmd['source_sha256'] == snapshot['files'][rel]
        assert cmd['output_sha256'] == rec['output_sha256']
        if cmd.get('status') == 'reused_exact_successful_local_output':
            prior = Path(cmd['prior_receipt']).parent.name
            assert receipt_hashes[prior] == cmd['prior_receipt_sha256']
            assert cmd['transitive_source_hashes'] == {proof[d]: snapshot['files'][proof[d]] for d in closure(mod)}
            chain.append({'run': run, 'prior': prior, 'prior_receipt_sha256': receipt_hashes[prior]})
            reuse_edges += 1; run = prior; continue
        assert cmd['exit_code'] == 0
        assert cmd['argv'][0:4] == [env['compiler'], '--threads=1', '--memory=4096', '-o']
        assert cmd['argv'][-1] == rel and cmd['argv'][-2].endswith('/' + rel[:-5] + '.olean')
        assert cmd['dependency_olean_sha256'] == {d: records[d]['output_sha256'] for d in imports[mod]}
        check(E / rec['log'], cmd['log_sha256'])
        assert not re.search(r'\b(error|sorryAx)\b', (E / rec['log']).read_text())
        assert rec['fresh_success_run'] == run and rec['actual_fresh_command'] == cmd
        assert rec['reuse_chain'] == chain
        intervals.append((datetime.datetime.fromisoformat(cmd['start']), datetime.datetime.fromisoformat(cmd['end']), mod))
        break
for a, b in zip(sorted(intervals), sorted(intervals)[1:]): assert a[1] <= b[0]
axioms = {m[1]: [x.strip() for x in m[2].split(',')] for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", (E / 'logs/recovery-118/Solution.log').read_text())}
assert set(axioms) == set(names) and all(set(v) == allowed for v in axioms.values())
assert axioms == read(E / 'actual-axioms.json')
assert re.findall(r'^#assert_trust kernel (.+)$', (P / 'Solution.lean').read_text(), re.M) == names
type_audit = read(T / 'AUDIT.json')
check(T / 'AUDIT.json', pre['type_diagnostic_sha256'])
assert type_audit['receipt_sha256'] == receipt_hashes['recovery-118']
typelogs = [(T / (name + '.log')).read_bytes() for name in ['MI27SolutionTypes118', 'MI27ChallengeTypes118']]
assert typelogs[0] == typelogs[1] and sha(typelogs[0]) == type_audit['log_sha256']
assert re.findall(r'^TYPEJSON (\S+) ', typelogs[0].decode(), re.M) == names
assert re.findall(r'^LEVELJSON (\S+) ', typelogs[0].decode(), re.M) == names
for name, imported in [('MI27SolutionTypes118', 'Solution'), ('MI27ChallengeTypes118', 'Challenge')]:
    src = (T / (name + '.lean')).read_text()
    assert src.startswith('import ' + imported + '\nimport Lean\n')
    assert re.findall(r'let info ← getConstInfo `(\S+)', src) == names
    assert 'reprStr info.type' in src and 'reprStr info.levelParams' in src
    cmd = commands['recovery-118'][name]
    assert cmd['exit_code'] == 0
    check(T / (name + '.lean'), cmd['source_sha256'])
    check(T / (name + '.log'), cmd['log_sha256'])
    assert cmd['dependency_olean_sha256'] == {imported: commands['recovery-118'][imported]['output_sha256']}
for report in pre['final_nonauthor_reviews']['reports']:
    check(P / report['report'], report['report_sha256'])
    check(P / report['manifest'], report['manifest_sha256'])
metadata = read(P / 'formalization.yaml')
assert metadata['alignment']['final_declarations'] == ['NLA.MI27.logarithmic_commutator_bound']
assert {r['declaration'] for r in metadata['status']['main_results']} == set(names)
result = {'verdict': 'PASS_RETAINED_EVIDENCE_CONSISTENCY', 'head': subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(), 'proof_modules': len(proof), 'contracts_matching_frozen_headers_and_raw_types': len(names), 'receipts': len(receipts), 'reuse_edges': reuse_edges, 'pins': pins, 'type_log_bytes': len(typelogs[0]), 'axioms': sorted(allowed), 'limitation': 'No new Lean/Comparator execution; original compiler, dependency worktrees, and .olean files unavailable here. This independently authenticates retained evidence and source correspondence, not external execution.'}
(OUT / 'retained-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

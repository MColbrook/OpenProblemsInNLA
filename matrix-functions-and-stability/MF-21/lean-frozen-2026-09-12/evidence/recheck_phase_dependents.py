#!/usr/bin/env python3
"""Recheck every dependent of the phase repair; reuse only verified unaffected outputs."""
import ast
import datetime as dt
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'evidence/runs/20260921T005811719722Z/record.json'
PERMITTED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    baseline = json.loads(BASE.read_text())
    assert baseline['passed'] and len(baseline['runs']) == 125
    assert sha(BASE) == '497c98bffe6628a5adef5653adfb73cf25e04fd27f7306176aea9e34260842c5'
    runner = ast.parse((ROOT / 'verify_local.py').read_text())
    modules = next(ast.literal_eval(node.value) for node in runner.body
        if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'MODULES' for t in node.targets))
    assert modules == [r['source'] for r in baseline['runs']]
    current = {s: sha(ROOT / s) for s in modules}
    changed = {s for s in modules if current[s] != baseline['source_hashes'][s]}
    assert changed == {'MF21Restart/PhaseWindowRoots.lean'}
    assert current[next(iter(changed))] == '7992ba76a6919b9e38aa3758ff74205befe02238e515b66b96584c1848a8d5c8'
    for p in ['lean-toolchain', 'lake-manifest.json']:
        assert sha(ROOT / p) == baseline['pin_hashes'][p]
    assert sha(ROOT / 'verify_local.py') == baseline['runner_sha256']
    assert sha(ROOT / 'original-proof/solution.md') == baseline['manuscript_sha256']
    old_lakefile = (BASE.parent / 'lakefile.toml').read_bytes()
    new_lakefile = (ROOT / 'lakefile.toml').read_bytes()
    assert new_lakefile.count(b'"-M6144"') == 4
    assert new_lakefile.replace(b'"-M6144"', b'"-M4096"') == old_lakefile
    names = {str(Path(s).with_suffix('')).replace('/', '.'): s for s in modules}
    graph = {s: [names[name] for name in re.findall(r'^import\s+(\S+)', (ROOT / s).read_text(), re.M)
                 if name in names] for s in modules}
    affected = set(changed)
    while True:
        expanded = affected | {s for s, deps in graph.items() if affected.intersection(deps)}
        if expanded == affected:
            break
        affected = expanded
    assert {'MF21Restart/TargetProof.lean', 'MF21Restart.lean', 'Solution.lean', 'Audit.lean'} <= affected
    positions = {s: i for i, s in enumerate(modules)}
    for s in affected:
        assert all(positions[d] < positions[s] for d in graph[s]), s
    source_set = {p.relative_to(ROOT).as_posix() for p in ROOT.glob('*.lean')}
    for directory in ['MF21Restart', 'LeanFormalizations']:
        source_set.update(p.relative_to(ROOT).as_posix() for p in (ROOT / directory).rglob('*.lean'))
    assert source_set == set(modules)
    for r in baseline['runs']:
        assert r['exit_code'] == 0
        assert sha(ROOT / r['log']) == r['log_sha256']
        assert sha(ROOT / '.lake/build/lib/lean' / Path(r['source']).with_suffix('.olean')) == r['output_sha256']
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    heads = {}
    for package in manifest['packages']:
        path = ROOT / manifest['packagesDir'] / package['name']
        env = dict(os.environ, GIT_OPTIONAL_LOCKS='0')
        head = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True, env=env).strip()
        assert head == package['rev'] == baseline['package_heads'][package['name']]
        assert not subprocess.check_output(['git', '-C', str(path), 'status', '--porcelain', '--untracked-files=no'], text=True, env=env).strip()
        heads[package['name']] = head
    start = dt.datetime.now(dt.timezone.utc)
    folder = ROOT / 'evidence/runs' / (start.strftime('%Y%m%dT%H%M%S%fZ') + '-phase-recheck')
    folder.mkdir(parents=True, exist_ok=False)
    record = {'scope': 'Complete current target via recompilation of every affected local module and reuse of hash-validated unchanged dependency closures',
        'started_utc': start.isoformat(), 'passed': False, 'comparator': 'not_run',
        'baseline_record': str(BASE.relative_to(ROOT)), 'baseline_record_sha256': sha(BASE),
        'runner_sha256': sha(Path(__file__).resolve()), 'full_runner_sha256': sha(ROOT / 'verify_local.py'),
        'source_hashes': current, 'pin_hashes': {p: sha(ROOT / p) for p in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']},
        'package_heads': heads, 'manuscript_sha256': baseline['manuscript_sha256'],
        'changed_sources': sorted(changed), 'import_graph': graph, 'affected_sources': [s for s in modules if s in affected],
        'limits': {'local_threads': 1, 'local_memory_MiB': 4096, 'lake_build_memory_MiB': 6144},
        'configuration_compatibility': 'Exactly four library memory ceilings changed from4096 to6144; all explicit local compiler commands remain -j1 -M4096. No other Lake setting or dependency changed.',
        'runs': [], 'reused': [], 'output_hashes': {}}
    with open('/private/tmp/nla-lean-compiler.lock', 'a+') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        for source in modules:
            output = ROOT / '.lake/build/lib/lean' / Path(source).with_suffix('.olean')
            if source not in affected:
                prior = next(r for r in baseline['runs'] if r['source'] == source)
                record['reused'].append({'source': source, 'source_sha256': current[source],
                    'output_sha256': prior['output_sha256'], 'successful_baseline_log': prior['log'],
                    'reason': 'Source and all transitive local dependencies are unchanged; pinned external dependencies and output hash verified.'})
            else:
                command = ['lake', 'env', 'lean', '-j1', '-M4096', '-o', str(output.relative_to(ROOT)), source]
                print('Running: LEAN_NUM_THREADS=1 ' + ' '.join(command), flush=True)
                log = folder / (Path(source).stem + '.log')
                with log.open('w') as handle:
                    result = subprocess.run(command, cwd=ROOT, env=dict(os.environ, LEAN_NUM_THREADS='1'), stdout=handle, stderr=subprocess.STDOUT)
                entry = {'source': source, 'command': command, 'environment': {'LEAN_NUM_THREADS': '1'},
                    'exit_code': result.returncode, 'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log)}
                record['runs'].append(entry)
                if result.returncode:
                    print(log.read_text(), flush=True)
                    break
                entry['output_sha256'] = sha(output)
            record['output_hashes'][source] = sha(output)
        else:
            assert all(sha(ROOT / s) == h for s, h in current.items())
            assert all(sha(ROOT / s) == h for s, h in record['pin_hashes'].items())
            reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", (folder / 'Audit.log').read_text())
            expected = re.findall(r'^#print axioms (\S+)$', (ROOT / 'Audit.lean').read_text(), re.M)
            assert len(reports) == len(expected) == len(set(expected)) == 386
            assert sorted(n for n, _ in reports) == sorted(expected)
            record['axioms'] = {n: sorted(x.strip() for x in axioms.split(',') if x.strip()) for n, axioms in reports}
            assert all(set(a) <= PERMITTED for a in record['axioms'].values())
            record['passed'] = True
    record['finished_utc'] = dt.datetime.now(dt.timezone.utc).isoformat()
    (folder / 'record.json').write_text(json.dumps(record, indent=2) + '\n')
    (ROOT / 'evidence/latest-phase-recheck.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({'passed': record['passed'], 'compiled': len(record['runs']), 'reused': len(record['reused']), 'record': str((folder / 'record.json').relative_to(ROOT)), 'record_sha256': sha(folder / 'record.json')}, indent=2), flush=True)
    return 0 if record['passed'] else 1

if __name__ == '__main__':
    raise SystemExit(main())

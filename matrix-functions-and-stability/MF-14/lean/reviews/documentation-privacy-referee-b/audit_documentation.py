from pathlib import Path
import datetime, gzip, hashlib, io, json, subprocess, zipfile

D = Path(__file__).resolve().parents[2]
R = Path(__file__).resolve().parent
W = D / 'publication/MF14'
P = W / 'matrix-functions-and-stability/MF-14/lean'
proof = 'c89c859a6b21c399a99f5e9f5fb2b7f472c96657'
base = '71563f17926cd826a892c2bba0e294894ee57a5c'
snapshot = D / 'final-review-packets/MF14-v2-instance-alignment/REVIEW-SNAPSHOT.json'
sha = lambda b: hashlib.sha256(b).hexdigest()
def blob(rev, rel):
    return subprocess.check_output(['git', 'show', f'{rev}:{rel}'], cwd=W)
def git(*args):
    return subprocess.check_output(['git', *args], cwd=W).decode()
assert sha(snapshot.read_bytes()) == '10b1b576719a24d12d3a123a1180c2c89d26626a41367ef0abaf42001cb52892'
snap = json.loads(snapshot.read_text())
lean_checks = {}
for rel, expected in snap['Lean_sources'].items():
    actual = sha((P / rel).read_bytes())
    assert actual == expected == sha(blob(proof, str((P / rel).relative_to(W)))), rel
    lean_checks[rel] = actual
assert len(lean_checks) == 87
configs = ['comparator.json', 'lake-manifest.json', 'lakefile.toml', 'lean-toolchain', 'STATEMENT-FREEZE.json']
config_checks = {}
for rel in configs:
    value = sha((P / rel).read_bytes())
    assert value == sha(blob(proof, str((P / rel).relative_to(W)))), rel
    if rel == 'lake-manifest.json':
        old_manifest = json.loads((snapshot.parent / rel).read_text())
        new_manifest = json.loads((P / rel).read_text())
        assert old_manifest['name'] == 'NLAPF03' and new_manifest['name'] == 'NLAMF14Degree44'
        old_manifest['name'] = new_manifest['name']
        assert old_manifest == new_manifest, 'only previously disclosed top-level Lake project name correction allowed'
    elif rel == 'lakefile.toml':
        old_lakefile = (snapshot.parent / rel).read_bytes()
        adjusted = old_lakefile.replace(b'name = "NLAMF14"\n', b'name = "NLAMF14Degree44"\n', 1).replace(b'# Build the proof environment. Challenge is isolated and used only for comparison.', b'# Solution must be assembled and checked before publication; Challenge is isolated.', 1)
        assert adjusted == (P / rel).read_bytes(), 'only prior project-name and comment packaging edits allowed'
    else:
        assert value == snap['files'][rel], rel
    config_checks[rel] = value
assert not git('diff', '--name-only', proof, '--', 'tools/lean', '.github/workflows/lean-verification.yml', 'problem_ids.json', 'references/webb-mf14-degree44-2026-09-17', 'references/webb-mf14-degree47-2026-09-17').strip()
canonical = W / 'matrix-functions-and-stability/MF-14/README.md'
def original_question(text):
    return text.split('## Problem statement\n', 1)[1].split('\n## ', 1)[0]
assert original_question(canonical.read_text()) == original_question(blob(base, str(canonical.relative_to(W))).decode())

privacy = json.loads((P / 'verification/PRIVACY-REDACTIONS.json').read_text())
mapping = {r['file']: r for r in privacy['files']}
secret_values = set()
redaction_checks = []
def leaves(a, b, path=''):
    if isinstance(a, dict):
        assert isinstance(b, dict) and a.keys() == b.keys(), path
        return sum([leaves(a[k], b[k], path + '/' + k) for k in a], [])
    if isinstance(a, list):
        assert isinstance(b, list) and len(a) == len(b), path
        return sum([leaves(x, y, path + '/' + str(i)) for i, (x, y) in enumerate(zip(a, b))], [])
    return [] if a == b else [(path, a, b)]

evidence_trees = [
    ('verification/linux-2026-09-19', D / 'verification/MF14-repaired-linux-20260919'),
    ('verification/linux-failed-fe4bbee-2026-09-19', D / 'verification/MF14-linux-20260919'),
    ('reviews/runtime-referee-b', D / 'reviews/MF14-repaired-runtime-referee-b'),
    ('reviews/runtime-failed-fe4bbee', D / 'reviews/MF14-runtime-referee-b'),
]
copied_files = []
new_public_metadata = []
for public_rel, local_dir in evidence_trees:
    for target in sorted((P / public_rel).rglob('*')):
        if not target.is_file():
            continue
        rel = str(target.relative_to(P))
        original = local_dir / target.relative_to(P / public_rel)
        if rel == 'verification/linux-2026-09-19/ORIGINAL-AUDIT-SCRIPT.py':
            original = D / 'recovery-tools/audit_target_linux.py'
        if rel == 'verification/linux-2026-09-19/SUMMARY.json':
            new_public_metadata.append({'file': rel, 'sha256': sha(target.read_bytes()), 'role': 'New public root-authored summary, not an original official response; independently read against actual runtime evidence.'})
            continue
        assert original.is_file(), ('original missing', rel)
        old, new = original.read_bytes(), target.read_bytes()
        if rel in mapping:
            m = mapping[rel]
            assert sha(old) == m['original_sha256'], rel
            assert sha(new) == m['published_redacted_sha256'], rel
            changes = leaves(json.loads(old), json.loads(new))
            assert len(changes) == m['replacements'] == 2, rel
            email_changes = [(path, x, y) for path, x, y in changes if path.endswith('/email')]
            assert len(email_changes) == 1, rel
            _, x, y = email_changes[0]
            assert isinstance(x, str) and '@' in x
            assert isinstance(y, str) and '@' not in y and 'redact' in y.lower()
            secret_values.add(x.encode())
            for path, before, after in changes:
                assert path.endswith('/email') or path.endswith('/verification/payload'), path
                assert before.replace(x, y) == after, path
            assert old.count(x.encode()) == 2, rel
            assert old.replace(x.encode(), y.encode()) == new, ('additional byte edit', rel)
            redaction_checks.append({'file': rel, 'original_sha256': sha(old), 'public_sha256': sha(new), 'only_changed_json_paths': [x[0] for x in changes], 'replacement_count': len(changes)})
        else:
            assert old == new, ('unmapped difference', rel)
        copied_files.append({'public_file': rel, 'public_sha256': sha(new), 'local_original_sha256': sha(old)})
assert len(redaction_checks) == len(mapping) == 4
assert len(secret_values) >= 1
scanned = 0
archive_members = 0
def scan_bytes(data, label, depth=0):
    global archive_members
    assert depth <= 5, label
    for secret in secret_values:
        assert secret.lower() not in data.lower(), ('private contributor contact remains', label)
    if data.startswith(b'\x1f\x8b'):
        archive_members += 1
        scan_bytes(gzip.decompress(data), label + '::gzip', depth + 1)
    elif data.startswith(b'PK\x03\x04'):
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            for name in archive.namelist():
                if not name.endswith('/'):
                    archive_members += 1
                    scan_bytes(archive.read(name), label + '::' + name, depth + 1)
for target in sorted((P.parent).rglob('*')):
    if target.is_file():
        scanned += 1
        scan_bytes(target.read_bytes(), str(target.relative_to(W)))
for rel in ['README.md', 'RESOLVED.md', 'CATALOG.md', 'matrix-functions-and-stability/README.md']:
    scan_bytes((W / rel).read_bytes(), rel)

metadata_paths = [canonical, W / 'RESOLVED.md', P / 'README.md', P / 'formalization.yaml', P / 'STATE.json', P / 'verification/PRIVACY-REDACTIONS.json', P / 'PACKAGING-NEXT-STEPS.md', P / 'IMPLEMENTATION-MAP.json']
metadata_hashes = {str(p.relative_to(W)): sha(p.read_bytes()) for p in metadata_paths}
formalization = json.loads((P / 'formalization.yaml').read_text())
state = json.loads((P / 'STATE.json').read_text())
assert formalization['status']['whole_problem_verified'] is True
assert formalization['status']['completed_original_targets'] == 1
assert len(formalization['status']['main_results']) == 25
assert state['degree47_claim_formalized_by_this_route'] is False
assert state['github_comparator'] == state['GitHub_Comparator'] == formalization['verification']['GitHub_Comparator']
v = formalization['verification']
for record_key, hash_key in [('root_audit','root_audit_sha256'), ('independent_audit','independent_audit_sha256'), ('runtime_review','runtime_review_sha256')]:
    g = v['GitHub_Comparator']
    assert sha((P / g[record_key]).read_bytes()) == g[hash_key], record_key
for rec in [v['local_aggregate'], v['statement_type_diagnostic']]:
    assert sha((P / rec['record']).read_bytes()) == rec['record_sha256']
for rec in v['final_independent_reviews']['reports'] + v['final_independent_reviews']['continuation_reports']:
    for field in ['report', 'manifest']:
        assert sha((P / rec[field]).read_bytes()) == rec[field + '_sha256'], rec[field]
result = {
    'verdict': 'PASS bounded documentation/source-hash/privacy audit',
    'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'reviewer': '/root/nr04_mf14_final_referee_b',
    'no_compiler_or_comparator_execution': True,
    'worktree': str(W),
    'current_head': git('rev-parse', 'HEAD').strip(),
    'verified_proof_commit': proof,
    'reviewed_snapshot_sha256': sha(snapshot.read_bytes()),
    'metadata_hashes': metadata_hashes,
    'Lean_sources_unchanged': lean_checks,
    'configs_unchanged': config_checks,
    'snapshot_config_exception': 'Before the verified proof commit, the Lake manifest top-level project name was corrected from NLAPF03 to NLAMF14Degree44 and the lakefile name from NLAMF14 to NLAMF14Degree44, with one lakefile comment changed. All other manifest/lakefile fields and every dependency pin agree with the frozen snapshot. Current bytes equal the actually verified proof commit.',
    'original_question_unchanged_from_base': base,
    'shared_verifier_and_degree44_degree47_source_archives_unchanged': True,
    'public_evidence_files_matched_to_originals': copied_files,
    'new_public_metadata': new_public_metadata,
    'redactions': redaction_checks,
    'privacy_scan': {'project_files': scanned, 'decompressed_archive_members': archive_members, 'additional_catalog_files': 4, 'remaining_known_contributor_contact_matches': 0, 'scope': 'raw file bytes and recursive gzip/zip members; no PDF text renderer invoked'},
    'metadata_review_scope': 'Current uncommitted promotion; actual execution claims remain bound to immutable proof commit. No new execution claimed.'
}
(R / 'AUDIT.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'verdict': result['verdict'], 'Lean_sources': len(lean_checks), 'configs': len(config_checks), 'matched_public_evidence_files': len(copied_files), 'redacted_derivatives': len(redaction_checks), 'privacy_scan': result['privacy_scan'], 'audit_sha256': sha((R / 'AUDIT.json').read_bytes())}, indent=2))

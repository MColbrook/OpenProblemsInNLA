#!/usr/bin/env python3
"""Independent read-only metadata audit. No compiler, subprocess, Git or network."""
from pathlib import Path
from hashlib import sha256
import json, re
import jsonschema

B = Path('/private/tmp/nla-lean-next-20260915')
D = B / 'MI28-publication-docs-draft'
S = B / 'MI28-local365-source-snapshot'
C = S / 'candidate'
EXPECTED_D = '3f35c783a327e8e5b67165558dcb9fd557d0a8e3de4d1ea8324f73bfed06b31d'
EXPECTED_S = '7054f5dd7c6bfcd03916565315495d463ccd3fc39db72fad13d19f81d389c089'
read_hashes = {}

def data(p):
    b = p.read_bytes()
    read_hashes[str(p)] = sha256(b).hexdigest()
    return b

def J(p): return json.loads(data(p))
def H(p): return sha256(data(p)).hexdigest()
def seal(p, expected):
    assert H(p / 'MANIFEST.json') == expected
    m = J(p / 'MANIFEST.json')
    for name, digest in m['files'].items():
        assert H(p / name) == digest, name
    actual = {str(x.relative_to(p)) for x in p.rglob('*') if x.is_file()}
    assert actual == set(m['files']) | {'MANIFEST.json'}, (p, actual ^ (set(m['files']) | {'MANIFEST.json'}))
    return m

md = seal(D, EXPECTED_D)
ms = seal(S, EXPECTED_S)
f = J(D / 'formalization.yaml')
schema_path = D / 'source-inputs/standards/v0.4.schema.json'
assert H(schema_path) == '25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce'
schema = J(schema_path)
validator = jsonschema.validators.validator_for(schema)
validator.check_schema(schema)
validator(schema).validate(f)

old_toml = data(C / 'lakefile.toml').decode()
new_toml = data(D / 'lakefile.toml').decode()
assert old_toml.count('defaultTargets = ["Challenge"]') == 1
assert new_toml == old_toml.replace('defaultTargets = ["Challenge"]', 'defaultTargets = ["Solution"]')
assert 'name = "NLAMI28"' in new_toml
old_lock, new_lock = J(C / 'lake-manifest.json'), J(D / 'lake-manifest.json')
assert old_lock['name'] == 'NLAMI22' and new_lock['name'] == 'NLAMI28'
old_lock['name'] = 'NLAMI28'
assert old_lock == new_lock
assert len(new_lock['packages']) == 10
assert data(C / 'lean-toolchain') == data(D / 'lean-toolchain')

im = J(D / 'IMPLEMENTATION-MAP.json')
scope = J(D / 'DOCUMENT-SCOPE.json')
assert im['proof_sources_sha256'] == scope['expected_proof_sources']
assert len(im['proof_sources_sha256']) == 52
for name, digest in im['proof_sources_sha256'].items(): assert H(C / name) == digest
for name, digest in scope['expected_frozen_files'].items(): assert H(C / name) == digest
headers = J(C / 'HEADERS.json')
comp = J(C / 'comparator.json')
contracts = im['contracts']
results = f['status']['main_results']
assert len(headers) == len(contracts) == len(results) == len(comp['theorem_names']) == 20
assert [x['contract'] for x in contracts] == [f'C{i:02d}' for i in range(1, 21)]
assert [x['declaration'] for x in contracts] == comp['theorem_names']
assert set(headers) == set(comp['theorem_names'])
assert comp['challenge_module'] == 'Challenge' and comp['solution_module'] == 'Solution'
assert comp['definition_names'] == []
for item, result in zip(contracts, results):
    for key in ['contract', 'declaration', 'file', 'source_sha256']:
        assert result[key] == item[key], (item['contract'], key)
    header = headers[item['declaration']]
    assert sha256(header['header'].encode()).hexdigest() == header['sha256'] == item['frozen_header_sha256']
    assert header['header'] in data(C / item['file']).decode()
    assert item['source_sha256'] == H(C / item['file'])
    assert result['sorry_count'] == 0
    assert result['axioms'] == comp['permitted_axioms']
    assert result['literature_dependencies'] == []
    assert 'GitHub Comparator NOT RUN' in result['verification_status']

assert f['project']['authors'] == ['George Stepaniants']
assert f['project']['affiliation'] == 'Department of Computing and Mathematical Sciences, California Institute of Technology'
assert f['status']['final_Linux_status'] == 'NOT RUN'
assert f['status']['local_type_diagnostic']['Comparator'] == 'NOT RUN'
assert f['status']['local_proof']['standalone_Lake_build'] == 'NOT RUN'
assert f['status']['accepted_count_change'] == 0
assert f['status']['sorry_count'] == f['status']['sorry_in_definitions'] == 0
assert f['status']['deliberate_challenge_placeholders'] == 20
assert f['alignment']['extra_substantive_hypotheses'] is False
assert f['alignment']['canonical_path'] == 'matrix-inequalities-and-norms/MI-28/README.md'
assert f['alignment']['formal_proof'] == 'NLA.MI28.determinant_comparison'
assert f['alignment']['stronger_result'] == 'NLA.MI28.full_log_majorization'
state = J(D / 'STATE.json')
assert state['local_compilation'] == f['status']['local_proof']
assert state['local_type_and_body_diagnostics'] == f['status']['local_type_diagnostic']
assert state['accepted_Lean_verification_count_change'] == state['new_mathematical_resolution_count_change'] == 0
readme = data(D / 'README.md').decode()
assert 'Historical records:' in readme and 'history/statement-draft/' in readme
assert 'UNELABORATED' in readme and 'not commands executed by this documentation task' in readme
assert 'NOT RUN' in readme and 'MI-28 was already **Solved**' in readme
# Privacy scope: newly authored metadata and supplied original canonical records.
privacy_paths = [p for p in D.rglob('*') if p.is_file() and p.suffix in {'.md', '.json', '.yaml', '.toml'}]
email = re.compile(r'(?<![A-Za-z0-9_.+%-])[A-Za-z0-9_.+%-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}')
for p in privacy_paths:
    assert not email.search(data(p).decode()), p

integration = J(D / 'INTEGRATION-REQUIREMENTS.json')
assert integration['canonical_publication_directory'] == 'matrix-inequalities-and-norms/MI-28/lean'
assert integration['count_change_authorized_by_this_draft'] == 0
for old in integration['archive_historical_records']:
    assert H(C / old['source']) == old['sha256']
assert integration['canonical_aggregate_mapping']['sha256'] == H(C / 'Solution.lean')

out = {
  'verdict': 'PASS',
  'scope': 'Independent nonauthor read-only metadata/schema/hash audit; not Lean, Lake, kernel, Comparator, Git or network execution.',
  'docs_manifest_sha256': EXPECTED_D,
  'source_manifest_sha256': EXPECTED_S,
  'draft_payload_files': len(md['files']),
  'snapshot_payload_files': len(ms['files']),
  'proof_modules_authenticated': 52,
  'frozen_headers_and_metadata_bindings': 20,
  'unchanged_dependency_objects': len(new_lock['packages']),
  'only_config_changes': ['defaultTargets Challenge to Solution', 'manifest root name NLAMI22 to NLAMI28'],
  'historical_labels_and_archives': 'PASS',
  'author_department_university_and_no_email': 'PASS',
  'status_and_pending_checks': 'PASS',
  'proof_source_mutations': 0,
  'compiler_executions': 0,
  'count_change': 0,
  'canonical_package_audit': 'Separate and pending exact root package seal',
  'read_files': len(read_hashes)
}
print(json.dumps(out, indent=2))

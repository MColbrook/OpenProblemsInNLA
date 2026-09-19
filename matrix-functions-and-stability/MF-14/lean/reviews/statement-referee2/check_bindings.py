#!/usr/bin/env python3
"""Read-only statement provenance audit. Never invokes Lean or Comparator."""
from pathlib import Path
import datetime
import difflib
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REC = ROOT / '.local-recovery-20260918'
PACKET = REC / 'development/MF14-degree44-statements-v2'
V1 = REC / 'development/MF14-degree44-statements-v1'
PUB = REC / 'publication/PF03'
OLD = REC / 'MF14-statement-gate-recovery-v1'
RUBRIC = PUB / 'eigenvalues-and-inverse-problems/KE-04/lean/reviews/final-referee-2-evidence'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda p: json.loads(p.read_text())

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

handoff = read(PACKET / 'STAGING-HANDOFF.json')
require(sha(PACKET / 'STAGING-HANDOFF.json') ==
        '08bf0681f405454e4725e7dfaaaae279a1582abd1c698c2e7bc6e377cc5db3d1', 'handoff hash')
for name, expected in handoff['files_sha256'].items():
    require(sha(PACKET / name) == expected, 'handoff input: ' + name)
sources = read(PACKET / 'SOURCE-INPUTS.json')
for name, expected in sources['inputs_sha256'].items():
    require(sha(ROOT / name) == expected, 'source provenance: ' + name)
header = read(PACKET / 'HEADER-CHECK.json')
for name, expected in header['source_sha256'].items():
    require(sha(PACKET / name) == expected, 'header input: ' + name)

challenge = (PACKET / 'Challenge.lean').read_text()
names = ['NLA.MF14Degree44.' + name
         for name in re.findall(r'^theorem\s+(\w+)', challenge, re.M)]
config = read(PACKET / 'comparator.json')
require(len(names) == len(set(names)) == 25, '25 distinct theorem headers')
require(names == config['theorem_names'], 'ordered Comparator names')
require(config['definition_names'] == [], 'definition mapping')
require(config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound'], 'axiom list')
require(len(re.findall(r'\bsorry\b', challenge)) == 25, 'Challenge placeholders')
require(not list(PACKET.rglob('*Solution*')), 'no solution in statement packet')
for file in PACKET.rglob('*.lean'):
    if file.name != 'Challenge.lean':
        require(not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b', file.read_text()),
                'no non-Challenge placeholders/axioms: ' + str(file))

diffs = {}
for file in PACKET.rglob('*.lean'):
    rel = file.relative_to(PACKET)
    before, after = (V1 / rel).read_text(), file.read_text()
    if before != after:
        diffs[str(rel)] = ''.join(difflib.unified_diff(
            before.splitlines(True), after.splitlines(True), fromfile='v1', tofile='v2'))
        require(str(rel) == 'NLA/MF14Degree44/Definitions.lean' and
                after.replace('import Mathlib.Analysis.InnerProductSpace.Defs\n', '', 1) == before,
                'only the declared import repair')
require(len(diffs) == 1, 'exactly one import-only changed Lean file')

freeze = read(OLD / 'MF14-STATEMENT-FREEZE-local275.json')
for name in ['Challenge.lean', 'comparator.json']:
    require(sha(OLD / name) == freeze['frozen_files'][name], 'old frozen file: ' + name)
require(sha(PACKET / 'NLA/MF14/Definitions.lean') ==
        freeze['frozen_files']['NLA/MF14/Definitions.lean'], 'unchanged original definitions')
require(len(read(OLD / 'comparator.json')['theorem_names']) == 27, 'old 27-contract gate')

receipt_path = Path(header['receipt'])
require(sha(receipt_path) == header['receipt_sha256'] ==
        '820ceae2ddc164184dcc45b3253002eca3a4489d730dcc4149352764accbfb5c', 'receipt hash')
receipt = read(receipt_path)
require(receipt['failed_modules'] == receipt['blocked_modules'] == [], 'header run failures')
require(receipt['threads'] == receipt['max_compiler_processes'] == 1 and
        receipt['memory_cap_mib'] == 4096, 'serial compiler limits as recorded')
logs = {}
for command in receipt['commands']:
    module = command['module']
    rel = 'Challenge.lean' if module == 'MF14Degree44Challenge' else module.replace('.', '/') + '.lean'
    require(command['source_sha256'] == sha(PACKET / rel), 'receipt source binding: ' + module)
    recorded_rel = 'MF14Degree44Challenge.lean' if module == 'MF14Degree44Challenge' else rel
    require(receipt['source_inputs'][recorded_rel] == sha(PACKET / rel), 'receipt inventory: ' + module)
    if 'exit_code' in command:
        require(command['exit_code'] == 0, 'recorded elaboration result: ' + module)
        require('--threads=1' in command['argv'] and '--memory=4096' in command['argv'], 'argv limits')
        file = receipt_path.parent / (module + '.log')
        require(sha(file) == command['log_sha256'], 'log binding: ' + module)
        text = file.read_text()
        require('error:' not in text, 'log errors: ' + module)
        require(text.count('warning: declaration uses `sorry`') ==
                (25 if module == 'MF14Degree44Challenge' else 0), 'expected draft warnings')
        logs[str(file.relative_to(ROOT))] = sha(file)

chain = []
current = receipt_path
while True:
    data = read(current)
    c = next(c for c in data['commands'] if c['module'] == 'NLA.MF14.Definitions')
    require(c['source_sha256'] == sha(PACKET / 'NLA/MF14/Definitions.lean'), 'reuse source hash')
    require(c['output_sha256'] == '5d1820746b89f87ebd02ba7fdd2a653f1f28a9e6147ef80d59016f461b897dcf',
            'reuse output hash')
    chain.append({'receipt': str(current.relative_to(ROOT)), 'sha256': sha(current),
                  'status': c.get('status', 'compiled'), 'exit_code': c.get('exit_code')})
    if 'prior_receipt' not in c:
        require(c['exit_code'] == 0, 'origin successful compilation')
        break
    previous = Path(c['prior_receipt'])
    require(sha(previous) == c['prior_receipt_sha256'], 'reuse prior receipt hash')
    current = previous
    require(len(chain) < 100, 'reuse loop')

symbolic = read(PUB / 'references/webb-mf14-degree44-2026-09-17/verification/symbolic_certificate.json')
degeneration = (PACKET / 'NLA/MF14Degree44/Degeneration.lean').read_text()
for i in range(1, 6):
    match = re.search(r'def syzygyCoefficient' + str(i) +
                     r' \(alpha eta gamma s : ℂ\) : ℂ :=\s*(.*?)\n\ndef', degeneration, re.S)
    require(match is not None and match.group(1).strip() == symbolic['E_s_cofactors'][i - 1],
            'literal source cofactor ' + str(i))

archive = read(RUBRIC / 'source-audit/result.json')['api_inputs']
rubric_bindings = {}
for file in sorted((RUBRIC / 'consulted-api/tauceti/rubrics').glob('*.md')):
    item = archive['verification/api-evidence-complete/tauceti/rubrics/' + file.name]
    raw = file.read_bytes()
    blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
    require(item['commit'] == 'afb424eda89e8ac96d9eb69f6a88972055a4cd1b' and
            sha(file) == item['sha256'] and blob == item['git_blob'], 'pinned rubric ' + file.name)
    rubric_bindings[file.name] = {'sha256': sha(file), 'git_blob': blob}

result = {
    'reviewer': '/root/mf14_degree44_statement_referee3',
    'time_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'scope': 'Independent byte/header/log audit only; not mathematical proof verification.',
    'status': 'PASS', 'lean_invoked_by_reviewer': False, 'comparator_invoked_by_reviewer': False,
    'handoff_sha256': sha(PACKET / 'STAGING-HANDOFF.json'),
    'receipt_sha256': sha(receipt_path), 'ordered_theorem_names': names,
    'challenge_placeholder_count': 25, 'v1_to_v2_lean_diff': diffs,
    'all_packet_manifest_hashes_match': True, 'all_source_input_hashes_match': True,
    'old_27_contract_gate_and_target_definitions_unchanged': True,
    'five_syzygy_expressions_literal_source_match': True,
    'inspected_logs_sha256': logs, 'recorded_header_commands': receipt['commands'],
    'shared_definition_reuse_chain': chain,
    'pinned_rubric_archive_bindings': rubric_bindings,
    'script_sha256': sha(Path(__file__)),
}
(HERE / 'BINDING-AUDIT.json').write_text(json.dumps(result, indent=2) + '\n')
print('PASS: sealed hashes, 25 exact Comparator names, header receipt/logs, reuse chain, old gate, and pinned rubric archive.')
print('No Lean, Comparator, or mathematical certificate verifier was invoked.')

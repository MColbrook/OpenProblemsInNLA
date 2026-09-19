"""Referee hash/source audit only; does not invoke Lean or execute receipts."""
from pathlib import Path
import datetime
import gzip
import hashlib
import json
import re

D = Path(__file__).resolve().parents[2]
P = D / "final-review-packets/MF14-v2-instance-alignment"
A = D / "verification/MF14-repair095-local-20260919"
sha = lambda b: hashlib.sha256(b).hexdigest()
snapshot = json.loads((P / "REVIEW-SNAPSHOT.json").read_text())
audit = json.loads((A / "LOCAL-REPLAY-AUDIT.json").read_text())
assert sha((P / "REVIEW-SNAPSHOT.json").read_bytes()) == "10b1b576719a24d12d3a123a1180c2c89d26626a41367ef0abaf42001cb52892"
assert sha((A / "LOCAL-REPLAY-AUDIT.json").read_bytes()) == "e514221a1ef727416004506ee71ad461aba5f8e110c91d3eb2c5be6909d5f408"
for path, digest in snapshot["files"].items():
    assert sha((P / path).read_bytes()) == digest, path
receipts = {}
for run, entry in audit["lossless_original_receipts"].items():
    data = (A / entry["file"]).read_bytes()
    assert sha(data) == entry["gzip_sha256"], run
    raw = gzip.decompress(data)
    assert sha(raw) == entry["original_sha256"], run
    receipts[run] = json.loads(raw)

records = {r["module"]: r for r in audit["module_records"]}
assert len(records) == 86
edges = 0
for module, record in records.items():
    assert sha((P / record["source"]).read_bytes()) == record["source_sha256"], module
    command = record["actual_fresh_command"]
    assert command["source_sha256"] == record["source_sha256"]
    assert command["output_sha256"] == record["output_sha256"]
    assert command["exit_code"] == 0
    assert "--threads=1" in command["argv"] and "--memory=4096" in command["argv"]
    assert sha((A / record["log"]).read_bytes()) == command["log_sha256"], module
    origin_commands = receipts[record["fresh_success_run"]]["commands"]
    assert command in origin_commands
    for dep, dep_hash in command["dependency_olean_sha256"].items():
        assert records[dep]["output_sha256"] == dep_hash, (module, dep)
    expected_run = audit["aggregate_run"]
    for link in record["reuse_chain"]:
        assert link["run"] == expected_run
        assert link["prior_receipt_sha256"] == audit["lossless_original_receipts"][link["prior"]]["original_sha256"]
        matches = [c for c in receipts[link["run"]]["commands"] if c["module"] == module]
        assert len(matches) == 1
        reused = matches[0]
        assert reused["status"] == "reused_exact_successful_local_output"
        assert reused["prior_receipt_sha256"] == link["prior_receipt_sha256"]
        assert Path(reused["prior_receipt"]).parent.name == link["prior"]
        assert reused["source_sha256"] == record["source_sha256"]
        assert reused["output_sha256"] == record["output_sha256"]
        for path, digest in reused["transitive_source_hashes"].items():
            assert sha((P / path).read_bytes()) == digest, (module, path)
        expected_run = link["prior"]
        edges += 1
    assert expected_run == record["fresh_success_run"]

latest = receipts[audit["aggregate_run"]]
assert audit["aggregate_command"] in latest["commands"]
assert audit["aggregate_command"] == records["Solution"]["actual_fresh_command"]
assert latest["compiler_sha256"] == audit["compiler_sha256"]
assert latest["runner_sha256"] == audit["runner_sha256"]
challenge = [c for c in receipts["recovery-094"]["commands"] if c["module"] == "Challenge"]
assert len(challenge) == 1
assert challenge[0]["exit_code"] == 0
assert challenge[0]["source_sha256"] == snapshot["files"]["Challenge.lean"]


def uncomment(text):
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            i += 1
    assert depth == 0
    return "".join(out)


sources = {path: uncomment((P / path).read_text()) for path in snapshot["Lean_sources"]}
implementation = {k: v for k, v in sources.items() if k != "Challenge.lean"}
for path, text in implementation.items():
    assert not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b", text), path
    assert not re.search(r"^import\s+.*\bChallenge\b", text, re.M), path

contracts = json.loads((P / "comparator.json").read_text())
assert contracts["definition_names"] == []
assert len(contracts["theorem_names"]) == 25
normalized = lambda s: re.sub(r"\s+", "", s)
headers = {}
for qualified in contracts["theorem_names"]:
    name = qualified.rsplit(".", 1)[-1]
    pattern = rf"\btheorem\s+{name}\b(.*?):=\s*by"
    challenge_headers = re.findall(pattern, sources["Challenge.lean"], re.S)
    found = [(path, h) for path, text in implementation.items() for h in re.findall(pattern, text, re.S)]
    assert len(challenge_headers) == len(found) == 1, name
    assert normalized(challenge_headers[0]) == normalized(found[0][1]), name
    headers[qualified] = found[0][0]
axioms = json.loads((A / "actual-axioms.json").read_text())
assert set(axioms) == set(contracts["theorem_names"])
assert all(set(a) <= set(contracts["permitted_axioms"]) for a in axioms.values())
aggregate_log = (A / records["Solution"]["log"]).read_text()
for name, declared_axioms in axioms.items():
    assert f"'{name}' depends on axioms: [{', '.join(declared_axioms)}]" in aggregate_log
    assert f"#assert_trust kernel {name}" in sources["Solution.lean"]

result = {
    "scope": "Independent referee hashing and source inspection; no new compiler, Lake or Comparator run",
    "created_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "status": "PASS",
    "all_snapshot_file_hashes_checked": len(snapshot["files"]),
    "Lean_files": len(snapshot["Lean_sources"]),
    "source_and_fresh_log_records_checked": len(records),
    "compressed_and_uncompressed_receipts_checked": len(receipts),
    "reuse_edges_recursively_authenticated": edges,
    "all_fresh_dependency_outputs_match_reviewed_source_records": True,
    "all_reused_transitive_source_hashes_match_reviewed_snapshot": True,
    "publication_name_Solution_and_separate_Challenge_success_recorded": True,
    "separate_Challenge_is_only_statement_elaboration_evidence": True,
    "implementation_forbidden_token_scan": "PASS after nested comment removal",
    "Solution_imports_Challenge": False,
    "all_25_contract_signatures_whitespace_normalized_identical": True,
    "all_25_actual_axiom_reports_and_kernel_assertions_match": True,
    "contract_implementation_files": headers,
    "snapshot_sha256": sha((P / "REVIEW-SNAPSHOT.json").read_bytes()),
    "local_audit_sha256": sha((A / "LOCAL-REPLAY-AUDIT.json").read_bytes()),
    "script_sha256": sha(Path(__file__).read_bytes()),
    "count_increment": 0,
}

# Bind the complete continuation to the earlier approved packet and exact diff.
old = D / 'final-review-packets/MF14-v1'
old_snapshot = json.loads((old / 'REVIEW-SNAPSHOT.json').read_text())
changed = [p for p in sorted(old_snapshot['files'].keys() | snapshot['files'].keys())
           if old_snapshot['files'].get(p) != snapshot['files'].get(p)]
assert changed == ['NLA/MF14Degree44/Mod3Certificate.lean']
changed_source = (P / changed[0]).read_text()
addition = ('-- Keep this public contract on the frozen commutative-ring instance.\n'
            '-- Imports below the proof route also expose a field instance for ZMod 3.\n'
            'attribute [-instance] ZMod.instField in\n')
assert changed_source.count(addition) == 1
assert changed_source.replace(addition, '') == (old / changed[0]).read_text()
assert sha(changed_source.encode()) == '962a7033d3eaaba2c7121aafbf81543786d80eff58fb7bf89a8633df6147a78e'
assert snapshot['files']['Challenge.lean'] == old_snapshot['files']['Challenge.lean']
assert snapshot['files']['comparator.json'] == old_snapshot['files']['comparator.json']

# Authenticate actual diagnostic sources, successful commands, complete raw logs,
# and the imports that bind those commands to the reviewed reference/solution.
diag = D / 'development/MF14-type-diagnostics-093'
diag_commands = {}
diag_logs = {}
for run, module, dep in [('recovery-094', 'MF14ChallengeTypes093', 'Challenge'),
                         ('recovery-094', 'MF14SolutionTypes093', 'Solution'),
                         ('recovery-095', 'MF14SolutionTypes093', 'Solution')]:
    command = next(c for c in receipts[run]['commands'] if c['module'] == module)
    source = diag / (module + '.lean')
    log = D / f'local-lean/runs/{run}/{module}.log'
    assert command['exit_code'] == 0
    assert '--threads=1' in command['argv'] and '--memory=4096' in command['argv']
    assert sha(source.read_bytes()) == command['source_sha256']
    assert sha(log.read_bytes()) == command['log_sha256']
    expected = challenge[0]['output_sha256'] if dep == 'Challenge' else records['Solution']['output_sha256']
    assert command['dependency_olean_sha256'] == {dep: expected}
    text = source.read_text()
    assert text.startswith(f'import {dep}\nimport Lean\n')
    assert re.findall(r'let info ← getConstInfo `([^\n]+)', text) == contracts['theorem_names']
    assert text.count('reprStr info.type') == text.count('reprStr info.levelParams') == 25
    assert not any(t in text for t in ['toString info.type', 'sorry', 'axiom ', 'unsafe ', 'run_tac'])
    content = log.read_text()
    assert re.findall(r'^TYPEJSON (\S+) ', content, re.M) == contracts['theorem_names']
    assert re.findall(r'^LEVELJSON (\S+) ', content, re.M) == contracts['theorem_names']
    assert '...' not in content and 'error:' not in content
    diag_commands[f'{run}/{module}'] = command
    diag_logs[f'{run}/{module}'] = content
reference_log = diag_logs['recovery-094/MF14ChallengeTypes093']
old_log = diag_logs['recovery-094/MF14SolutionTypes093']
new_log = diag_logs['recovery-095/MF14SolutionTypes093']
assert reference_log == new_log
assert sha(new_log.encode()) == '5ff7380dc81ef84138c68db3dfadd700672b52698b02183c99fd471723ea4f77'
parse = lambda s: dict(re.findall(r'^TYPEJSON (\S+) (.*?)(?=^TYPEJSON |\Z)', s, re.M | re.S))
ref_blocks, old_blocks = parse(reference_log), parse(old_log)
mismatches = [n for n in contracts['theorem_names'] if ref_blocks[n] != old_blocks[n]]
assert mismatches == ['NLA.MF14Degree44.integer_jacobian_mod3_inverse']
assert '`ZMod.commRing' in ref_blocks[mismatches[0]]
assert '`ZMod.instField' not in ref_blocks[mismatches[0]]
assert '`ZMod.instField' in old_blocks[mismatches[0]]
assert '`Nat.fact_prime_three' in old_blocks[mismatches[0]]

# The Challenge command itself is fresh in 094, unchanged and source-bound.
for dep, digest in challenge[0]['dependency_olean_sha256'].items():
    assert records[dep]['output_sha256'] == digest
challenge_log = D / 'local-lean/runs/recovery-094/Challenge.log'
assert sha(challenge_log.read_bytes()) == challenge[0]['log_sha256']
assert challenge[0]['source_sha256'] == snapshot['files']['Challenge.lean']
fresh_changed_chain = [r['module'] for r in audit['module_records']
                       if r['fresh_success_run'] == 'recovery-095']
assert fresh_changed_chain == ['NLA.MF14Degree44.Mod3Certificate', 'NLA.MF14Degree44.JacobianNonzero',
                               'NLA.MF14Degree44.JacobianIdentity', 'NLA.MF14Degree44.FinalClosure', 'Solution']

result.update({
    'reviewer': '/root/nr04_mf14_final_referee_b',
    'verdict': 'APPROVE bounded source/evidence continuation; repaired GitHub Comparator remains pending',
    'changed_packet_files': changed,
    'single_declaration_scoped_instance_attribute_is_only_code_change': True,
    'all_25_raw_elaborated_type_and_universe_logs_byte_identical': True,
    'raw_reference_and_repaired_solution_log_sha256': sha(new_log.encode()),
    'old_raw_mismatches_independently_recomputed': mismatches,
    'fresh_changed_module_dependency_chain': fresh_changed_chain,
    'diagnostic_commands': diag_commands,
    'root_type_match_json_sha256': sha((D / 'development/MF14-instance-alignment-095/TYPE-MATCH.json').read_bytes()),
    'no_new_Lean_Lake_or_Comparator_by_reviewer': True,
    'repaired_GitHub_Comparator_success': 'NOT_YET_ESTABLISHED',
    'script_sha256': sha(Path(__file__).read_bytes()),
})
print(json.dumps(result, indent=2))

"""Referee hash/source audit only; does not invoke Lean or execute receipts."""
from pathlib import Path
import datetime
import gzip
import hashlib
import json
import re

D = Path(__file__).resolve().parents[2]
P = D / "final-review-packets/MF14-v1"
A = D / "verification/MF14-local-20260919"
sha = lambda b: hashlib.sha256(b).hexdigest()
snapshot = json.loads((P / "REVIEW-SNAPSHOT.json").read_text())
audit = json.loads((A / "LOCAL-REPLAY-AUDIT.json").read_text())
assert sha((P / "REVIEW-SNAPSHOT.json").read_bytes()) == "e52fab5a7b58c3bc6fb2c2df1283d55c6e4352056689c900de936c12e2595436"
assert sha((A / "LOCAL-REPLAY-AUDIT.json").read_bytes()) == "94021fa538957ad35044b9a6540fecf8a3ca99bcacd6546881cd3ac1b37e2cfa"
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
challenge = [c for c in latest["commands"] if c["module"] == "Challenge"]
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
print(json.dumps(result, indent=2))

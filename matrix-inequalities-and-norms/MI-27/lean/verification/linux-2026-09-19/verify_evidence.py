#!/usr/bin/env python3
"""Authenticate retained CI against immutable Git sources, not later metadata."""
from pathlib import Path
import hashlib
import json
import subprocess

EVIDENCE = Path(__file__).resolve().parent
PROJECT = EVIDENCE.parents[1]
ROOT = PROJECT.parents[2]
PROJECT_PATH = PROJECT.relative_to(ROOT).as_posix()
HEAD = "1f05b398013d44beb7d756cbfbbfd3e875c8deab"
RUN = EVIDENCE / "verify-20260919T104455Z-4157"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def original(path):
    return subprocess.check_output(["git", "show", f"{HEAD}:{path}"], cwd=ROOT)


result = json.loads((RUN / "result.json").read_text())
assert result["repository_commit"] == "f21284e35e8156a9761c1f2ccd49d579f42fb69a"
assert result["result"] == "comparator-accepted"
assert result["project"] == PROJECT_PATH
assert result["config"] == json.loads(original(f"{PROJECT_PATH}/comparator.json"))
assert len(result["input_sha256"]) == 284
for relative, expected in result["input_sha256"].items():
    assert digest(original(f"{PROJECT_PATH}/{relative}")) == expected, relative
    # Later publication may update live metadata; mathematical sources stay fixed.
    if (relative.startswith("NLA/") or relative in {
        "Challenge.lean", "Solution.lean", "comparator.json", "lean-toolchain",
        "lakefile.toml", "lake-manifest.json", "STATEMENT-FREEZE.json"
    }):
        assert digest((PROJECT / relative).read_bytes()) == expected, relative
assert digest(original("tools/lean/source-lock.json")) == result["source_lock_sha256"]
assert digest((EVIDENCE / "lean-MI-27.zip").read_bytes()) == (
    "50394e222707d250e7e1fc58dc80b8f6e59fb475b324a3414fd59f36e045b094"
)
audit = json.loads((EVIDENCE / "SOURCE-AUTHENTICATION.json").read_text())
for name, expected in audit["log_sha256"].items():
    assert digest((RUN / name).read_bytes()) == expected, name
print("PASS: 284 immutable CI inputs; live proof/contracts/pins unchanged; archive/log digests")

#!/usr/bin/env python3
"""Check the runner's lock portability and exclusion without starting Lean."""
from __future__ import annotations

import ast
import datetime as dt
import fcntl
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
RUN = ROOT / "evidence/runs/20260921T000301098707Z"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main_without_lock_path(path: Path) -> str:
    module = ast.parse(path.read_text())
    main = next(node for node in module.body
                if isinstance(node, ast.FunctionDef) and node.name == "main")
    changed = 0
    for node in ast.walk(main):
        if (isinstance(node, ast.Assign) and len(node.targets) == 1
                and isinstance(node.targets[0], ast.Name)
                and node.targets[0].id == "lock_path"):
            node.value = ast.Constant(value="REVIEWED_LOCK_PATH_SELECTION")
            changed += 1
    assert changed == 1
    return ast.dump(main, include_attributes=False)


def main() -> None:
    sys.dont_write_bytecode = True
    runner_path = ROOT / "verify_local.py"
    archive = RUN / "verify_local.py"
    proof_record = json.loads((RUN / "record.json").read_text())
    assert sha(archive) == proof_record["runner_sha256"]
    assert main_without_lock_path(archive) == main_without_lock_path(runner_path)

    spec = importlib.util.spec_from_file_location("mf21_runner_portability", runner_path)
    assert spec is not None and spec.loader is not None
    runner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(runner)  # Imports definitions only; never calls its main.

    selections = []
    for platform, temporary, expected in [
        ("darwin", "/ignored-for-macos", "/private/tmp/nla-lean-compiler.lock"),
        ("linux", "/tmp", "/tmp/nla-lean-compiler.lock"),
        ("linux", "/var/tmp", "/var/tmp/nla-lean-compiler.lock"),
    ]:
        with patch.object(runner.sys, "platform", platform), \
                patch.object(runner.tempfile, "gettempdir", return_value=temporary):
            actual = str(runner.compiler_lock_path())
            assert actual == expected
            selections.append({"platform": platform, "temporary_directory": temporary,
                               "selected": actual})

    child = """import fcntl, sys
with open(sys.argv[1], 'a+') as handle:
    try:
        fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        print('blocked')
    else:
        print('acquired')
"""
    with tempfile.TemporaryDirectory(prefix="mf21-lock-smoke-") as temporary:
        lock_path = Path(temporary) / "nla-lean-compiler.lock"
        with lock_path.open("a+") as handle:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
            blocked = subprocess.run([sys.executable, "-c", child, str(lock_path)],
                                     capture_output=True, text=True, check=True, timeout=10)
            assert blocked.stdout.strip() == "blocked"
        released = subprocess.run([sys.executable, "-c", child, str(lock_path)],
                                  capture_output=True, text=True, check=True, timeout=10)
        assert released.stdout.strip() == "acquired"

    drift = [source for source, digest in proof_record["source_hashes"].items()
             if sha(ROOT / source) != digest]
    assert not drift
    result = {
        "checked_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "result": "passed",
        "scope": "Python-only lock selection, actual two-process flock exclusion, "
                 "and runner main equivalence except lock selection; no Lean or "
                 "Comparator was executed. OS-selection cases are mocked; flock "
                 "exclusion runs on the recorded host.",
        "command": ["python3", "evidence/runner-portability-smoke.py"],
        "host_platform": sys.platform,
        "python_version": sys.version,
        "script_sha256": sha(Path(__file__)),
        "current_runner_sha256": sha(runner_path),
        "archived_runner": str(archive.relative_to(ROOT)),
        "archived_runner_sha256": sha(archive),
        "full_proof_record": str((RUN / "record.json").relative_to(ROOT)),
        "full_proof_record_sha256": sha(RUN / "record.json"),
        "selection_cases": selections,
        "held_lock_child": blocked.stdout.strip(),
        "released_lock_child": released.stdout.strip(),
        "main_unchanged_except_lock_selection": True,
        "proof_source_drift": drift,
    }
    (ROOT / "evidence/runner-portability-smoke.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print("PASS: portable selection and real lock exclusion; no Lean process started")


if __name__ == "__main__":
    main()

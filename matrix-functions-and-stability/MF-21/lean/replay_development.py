#!/usr/bin/env python3
"""Fresh source-only local replay; not the Linux Comparator verifier.

Uses only a newly created local olean directory and explicitly supplied,
manifest-listed external dependency caches. Never searches project oleans.
"""
from __future__ import annotations
import argparse
import concurrent.futures
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import time

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_code(text: str) -> str:
    """Remove nested Lean comments and strings, preserving line boundaries."""
    result, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == "/-": depth += 1; result.extend("  "); i += 2
            elif pair == "-/": depth -= 1; result.extend("  "); i += 2
            else: result.append("\n" if text[i] == "\n" else " "); i += 1
        elif string:
            if text[i] == "\\": result.extend("  "); i += 2
            elif text[i] == '"': string = False; result.append(" "); i += 1
            else: result.append("\n" if text[i] == "\n" else " "); i += 1
        elif pair == "/-": depth = 1; result.extend("  "); i += 2
        elif pair == "--":
            end = text.find("\n", i)
            if end < 0: end = len(text)
            result.extend(" " * (end-i)); i = end
        elif text[i] == '"': string = True; result.append(" "); i += 1
        else: result.append(text[i]); i += 1
    if depth or string:
        raise ValueError("Unterminated Lean comment/string")
    return "".join(result)


def imports(text: str) -> list[str]:
    return re.findall(r"(?m)^\s*(?:(?:public|private|meta)\s+)*import\s+([A-Za-z_][A-Za-z_0-9.]*)", lean_code(text))


def axiom_audit_source(modules: list[str]) -> str:
    # Auditing imported module tables includes private/generated declarations.
    # collectAxioms follows each declaration's actual transitive proof closure.
    return "\n".join("import " + name for name in modules) + '''
import Lean.Util.CollectAxioms
import Lean.Elab.Command
set_option maxHeartbeats 0
open Lean Elab Command
elab "audit_local_axioms" : command => do
  let wanted : Array String := #[MODULE_NAMES]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    if wanted.contains modName.toString then
      let data := env.header.moduleData[i]!
      for name in data.constNames do
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Forbidden axiom {ax} in {name} from {modName}"
        logInfo m!"REPLAY_AXIOMS {name}: {axioms}"
        count := count + 1
  if count == 0 then throwError "No local declarations found"
  logInfo m!"REPLAY_AUDITED_DECLARATIONS {count}"
audit_local_axioms
'''.replace("MODULE_NAMES", ", ".join(json.dumps(name) for name in modules))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--lean", type=Path, required=True, help="Exact Lean executable")
    parser.add_argument("--packages", type=Path, required=True, help="External Lake packages directory")
    parser.add_argument("--output", type=Path, required=True, help="New, nonexistent replay directory")
    parser.add_argument("--exclude", action="append", default=[], help="Exact local module to omit; repeatable")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--timeout", type=int, default=1800, help="Wall seconds per module")
    args = parser.parse_args()
    if args.jobs < 1: parser.error("--jobs must be positive")
    source, lean, packages, output = (p.resolve() for p in (args.source, args.lean, args.packages, args.output))
    if output.exists(): parser.error("--output already exists; fresh replay refuses reuse")
    if source == output or source in output.parents: parser.error("--output must be outside source tree")
    manifest = json.loads((source / "lake-manifest.json").read_text())
    external, dependencies = [], []
    for pkg in manifest["packages"]:
        if pkg["type"] != "git": parser.error("Only exact git dependency manifests are supported")
        cache = packages / pkg["name"] / ".lake/build/lib/lean"
        if pkg["name"] == "mathlib" and not cache.is_dir():
            parser.error(f"Missing mathlib cache {cache}")
        if cache.is_dir(): external.append(cache)
        check = subprocess.run(["git", "-C", str(packages/pkg["name"]), "rev-parse", "HEAD"], capture_output=True, text=True)
        actual = check.stdout.strip() if check.returncode == 0 else None
        if actual and actual != pkg["rev"]: parser.error(f"Dependency revision mismatch: {pkg['name']}")
        dependencies.append({"name":pkg["name"], "expected_revision":pkg["rev"], "observed_revision":actual,
            "cache":str(cache), "cache_present":cache.is_dir(), "revision_check":"matched" if actual else "unavailable; external cache trusted"})
    sources = {".".join(p.relative_to(source).with_suffix("").parts):p for p in source.rglob("*.lean")
        if ".lake" not in p.relative_to(source).parts and "Probe" not in p.name}
    unknown = set(args.exclude)-set(sources)
    if unknown: parser.error(f"Unknown exclusions: {sorted(unknown)}")
    selected = {m:p for m,p in sources.items() if m not in args.exclude}
    texts = {m:p.read_text() for m,p in selected.items()}
    graph = {m:sorted(set(imports(t)) & set(sources)) for m,t in texts.items()}
    for module, deps in graph.items():
        missing = set(deps)-set(selected)
        if missing: parser.error(f"{module} depends on excluded modules {sorted(missing)}; exclude it too")
    for module in selected:
        for cache in external:
            if (cache/Path(*module.split("."))).with_suffix(".olean").exists():
                parser.error(f"External cache shadows local module {module}")
    # Validate acyclicity before starting any compiler.
    order, pending = [], set(selected)
    while pending:
        ready = sorted(m for m in pending if set(graph[m]) <= set(order))
        if not ready: parser.error(f"Local import cycle: {sorted(pending)}")
        order.extend(ready); pending.difference_update(ready)
    output.mkdir(parents=True)
    frozen, compiled, logs = output/"source", output/"olean", output/"logs"
    for p in (frozen,compiled,logs): p.mkdir()
    hashes = {}
    for module, p in selected.items():
        dst = frozen/p.relative_to(source)
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_bytes(p.read_bytes())
        hashes[module] = sha256(dst)
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        shutil.copyfile(source/name, frozen/name)
    audit = axiom_audit_source(sorted(selected))
    (frozen/"ReplayAxiomAudit.lean").write_text(audit)
    env = os.environ.copy()
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
        env.pop(key, None)
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in [compiled]+external)
    version = subprocess.run([str(lean), "--version"],capture_output=True,text=True,check=True).stdout.strip()
    report = {"kind":"development source replay; not Linux Comparator", "status":"running",
        "started_utc":dt.datetime.now(dt.timezone.utc).isoformat(), "platform":platform.platform(),
        "lean":str(lean), "lean_sha256":sha256(lean), "lean_version":version,
        "toolchain":(source/"lean-toolchain").read_text().strip(),
        "manifest_sha256":sha256(source/"lake-manifest.json"), "runner_sha256":sha256(Path(__file__)),
        "source":str(source), "output":str(output), "lean_path":env["LEAN_PATH"],
        "dependencies":dependencies, "excluded_modules":sorted(args.exclude),
        "probe_policy":"Every filename containing Probe is excluded", "local_import_graph":graph,
        "source_sha256":hashes, "generated_audit_sha256":sha256(frozen/"ReplayAxiomAudit.lean"),
        "allowed_axioms":sorted(ALLOWED_AXIOMS), "modules":{}, "axiom_audit":None}
    def save(): (output/"result.json").write_text(json.dumps(report,indent=2)+"\n")
    save()
    def compile_one(module):
        relative = Path(*module.split("."))
        target = (compiled/relative).with_suffix(".olean")
        target.parent.mkdir(parents=True,exist_ok=True)
        log = logs/(module+".log")
        command = [str(lean),"--trust=0","-o",str(target),str(relative.with_suffix(".lean"))]
        start = time.monotonic()
        with log.open("w") as stream:
            try:
                process = subprocess.run(command,cwd=frozen,env=env,stdout=stream,stderr=subprocess.STDOUT,
                                         timeout=args.timeout)
                code = process.returncode
            except subprocess.TimeoutExpired: code = 124; stream.write("\nREPLAY_PROCESS_TIMEOUT\n")
        text = log.read_text()
        failures = []
        if code: failures.append(f"exit {code}")
        if re.search(r"\b(sorryAx|admit)\b|declaration uses .sorry.",text): failures.append("sorry/admit in output")
        for chunk in re.findall(r"depends on axioms:\s*\[([^]]*)\]",text):
            bad = set(a.strip() for a in chunk.split(",") if a.strip())-ALLOWED_AXIOMS
            if bad: failures.append(f"nonstandard printed axioms {sorted(bad)}")
        return {"command":command,"exit_code":code,"seconds":round(time.monotonic()-start,3),
            "log":str(log.relative_to(output)),"log_sha256":sha256(log),
            "olean_sha256":sha256(target) if target.exists() else None,"failures":failures,
            "printed_axiom_reports":len(re.findall("depends on axioms:",text))}
    done, running, pending, failed = set(), {}, set(selected), False
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            if not failed:
                ready = sorted(m for m in pending if set(graph[m]) <= done)
                for module in ready[:args.jobs-len(running)]:
                    print(f"START {module}",flush=True)
                    running[pool.submit(compile_one,module)] = module
                    pending.remove(module)
            if not running: break
            finished,_ = concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
            for future in finished:
                module = running.pop(future)
                result = future.result()
                report["modules"][module] = result
                if result["failures"]: failed=True
                else: done.add(module)
                print(f"{'FAIL' if result['failures'] else 'PASS'} {module} ({result['seconds']}s)",flush=True)
                if result["failures"]: print((logs/(module+".log")).read_text()[-5000:],flush=True)
                save()
    if not failed and len(done)==len(selected):
        print("START ReplayAxiomAudit",flush=True)
        report["axiom_audit"] = compile_one("ReplayAxiomAudit")
        failed = bool(report["axiom_audit"]["failures"])
        print(f"{'FAIL' if failed else 'PASS'} ReplayAxiomAudit",flush=True)
        if failed: print((logs/"ReplayAxiomAudit.log").read_text()[-5000:],flush=True)
    changed = [m for m,p in selected.items() if not p.exists() or sha256(p)!=hashes[m]]
    report["source_changed_since_snapshot"] = sorted(changed)
    report["unfinished_modules"] = sorted(pending)
    report["finished_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
    report["status"] = "failed" if failed else ("snapshot_passed_sources_changed" if changed else "passed")
    save()
    print(f"RESULT {report['status']}: {output/'result.json'}",flush=True)
    return 1 if failed or changed else 0

if __name__ == "__main__":
    raise SystemExit(main())

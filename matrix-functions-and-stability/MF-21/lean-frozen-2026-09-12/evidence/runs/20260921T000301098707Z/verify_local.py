#!/usr/bin/env python3
"""Compile MF-21 serially and retain source-matched full-target evidence."""
from __future__ import annotations

import datetime as dt
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
MODULES = [
    "MF21Restart/Definitions.lean",
    "MF21Restart/StatementBridges.lean",
    "MF21Restart/FixedIndex.lean",
    "MF21Restart/BulkDecay.lean",
    "MF21Restart/Numerics.lean",
    "MF21Restart/FourierStencil.lean",
    "MF21Restart/FourierLaurent.lean",
    "MF21Restart/FourierEndpoint.lean",
    "MF21Restart/FourierRecurrence.lean",
    "MF21Restart/BoundaryExpansion.lean",
    "MF21Restart/RecurrenceBasis.lean",
    "MF21Restart/BoundaryRecurrence.lean",
    "MF21Restart/FiniteRecurrence.lean",
    "MF21Restart/ToeplitzRecurrence.lean",
    "MF21Restart/TraceIntegral.lean",
    "MF21Restart/KernelDiagonal.lean",
    "LeanFormalizations/NumberTheory/Transcendence/ETranscendental.lean",
    "LeanFormalizations/NumberTheory/Transcendence/PiLindemann.lean",
    "LeanFormalizations/NumberTheory/Transcendence/HermiteLindemann.lean",
    "LeanFormalizations/NumberTheory/Transcendence/MonicRootSums.lean",
    "LeanFormalizations/NumberTheory/Transcendence/SubsetSumEsymm.lean",
    "LeanFormalizations/NumberTheory/Transcendence/PiTranscendental.lean",
    "MF21Restart/PiTranscendence.lean",
    "MF21Restart/TraceIrrationality.lean",
    "MF21Restart/FourierRecurrenceEquation.lean",
    "MF21Restart/BoundaryToeplitz.lean",
    "MF21Restart/EigenvalueBridge.lean",
    "MF21Restart/RealComplexEigenvalue.lean",
    "MF21Restart/TraceSeriesZeta.lean",
    "MF21Restart/TraceSeriesOdd.lean",
    "MF21Restart/TraceSeriesHalf.lean",
    "MF21Restart/TraceSeries.lean",
    "MF21Restart/StableRootAlgebra.lean",
    "MF21Restart/StableRootSmooth.lean",
    "MF21Restart/RootParameters.lean",
    "MF21Restart/PhaseFactor.lean",
    "MF21Restart/StableRootDecay.lean",
    "MF21Restart/RootDistinctness.lean",
    "MF21Restart/StableRootSymmetry.lean",
    "MF21Restart/StableRootBounds.lean",
    "MF21Restart/PhaseZero.lean",
    "MF21Restart/PhasePi.lean",
    "MF21Restart/BoundaryMultiplicity.lean",
    "MF21Restart/DeterminantMultiplicity.lean",
    "MF21Restart/SimpleDeterminant.lean",
    "MF21Restart/CharacteristicRoots.lean",
    "MF21Restart/ConcreteBoundary.lean",
    "MF21Restart/PhaseMonotonicity.lean",
    "MF21Restart/AnalyticSlope.lean",
    "MF21Restart/RootTangents.lean",
    "MF21Restart/EigenvalueMultiplicity.lean",
    "MF21Restart/VandermondeScale.lean",
    "MF21Restart/RootDifferences.lean",
    "MF21Restart/NormalizedBoundary.lean",
    "MF21Restart/CharacteristicSublist.lean",
    "MF21Restart/BoundaryProductDecay.lean",
    "MF21Restart/NormalizedQuotient.lean",
    "MF21Restart/NormalizedErrorCoefficient.lean",
    "MF21Restart/PhaseProduct.lean",
    "MF21Restart/BoundaryConjugation.lean",
    "MF21Restart/LeadingBoundaryIndices.lean",
    "MF21Restart/RootListProducts.lean",
    "MF21Restart/BoundaryNormalizer.lean",
    "MF21Restart/BoundaryErrorBounds.lean",
    "MF21Restart/LeadingBoundaryCoefficients.lean",
    "MF21Restart/LeadingNormalization.lean",
    "MF21Restart/DeterminantRemainder.lean",
    "MF21Restart/SpectralWindowBounds.lean",
    "MF21Restart/SpectralEnclosure.lean",
    "MF21Restart/WeightedBinomialInverse.lean",
    "MF21Restart/ActualSimpleRoots.lean",
    "MF21Restart/TriangularInverse.lean",
    "MF21Restart/FourierBinomialStencil.lean",
    "MF21Restart/PhaseWindowRoots.lean",
    "MF21Restart/MatrixInverseAlgebra.lean",
    "MF21Restart/FinalPhaseWindow.lean",
    "MF21Restart/ToeplitzWeightedFactorization.lean",
    "MF21Restart/ToeplitzInverse.lean",
    "MF21Restart/InverseKernelEntries.lean",
    "MF21Restart/PhaseRootCoverage.lean",
    "MF21Restart/SpectralOrder.lean",
    "MF21Restart/OrderedTailCounting.lean",
    "MF21Restart/PhaseWindowIndexing.lean",
    "MF21Restart/PhaseQuantitative.lean",
    "MF21Restart/EtaNeighborhood.lean",
    "MF21Restart/UniformImplicitScalar.lean",
    "MF21Restart/ImplicitPhase.lean",
    "MF21Restart/ParametricTaylor.lean",
    "MF21Restart/ImplicitTaylor.lean",
    "MF21Restart/VerticalPowerFactor.lean",
    "MF21Restart/CoefficientVanishing.lean",
    "MF21Restart/SymbolDerivative.lean",
    "MF21Restart/ImplicitSpectralError.lean",
    "MF21Restart/ImplicitSpectralData.lean",
    "MF21Restart/CirculantEmbedding.lean",
    "MF21Restart/CirculantSpectrum.lean",
    "MF21Restart/ScaledRising.lean",
    "MF21Restart/RiemannCellBound.lean",
    "MF21Restart/ScaledInverseSum.lean",
    "MF21Restart/KernelRiemannApprox.lean",
    "MF21Restart/KernelShiftedSum.lean",
    "MF21Restart/InverseKernelGridTop.lean",
    "MF21Restart/InverseKernelContinuity.lean",
    "MF21Restart/InverseKernelGrid.lean",
    "MF21Restart/InverseKernelLimit.lean",
    "MF21Restart/ActualKernelDiagonal.lean",
    "MF21Restart/GridAverage.lean",
    "MF21Restart/ActualTraceLimit.lean",
    "MF21Restart/CirculantOrder.lean",
    "MF21Restart/DiagonalInterlacing.lean",
    "MF21Restart/HermitianInterlacing.lean",
    "MF21Restart/CirculantBounds.lean",
    "MF21Restart/ExpansionScalar.lean",
    "MF21Restart/ExpansionAssembly.lean",
    "MF21Restart/ImplicitExpansionBounds.lean",
    "MF21Restart/SmoothCoefficient.lean",
    "MF21Restart/ExtensionIndependence.lean",
    "MF21Restart/InverseSpectralTrace.lean",
    "MF21Restart/ActualFixedIndex.lean",
    "MF21Restart/SpectralTracePassage.lean",
    "MF21Restart/TargetProof.lean",
    "MF21Restart.lean",
    "Solution.lean",
    "Challenge.lean",
    "Audit.lean",
]
PERMITTED = {"propext", "Classical.choice", "Quot.sound"}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    now = dt.datetime.now(dt.timezone.utc)
    stamp = now.strftime("%Y%m%dT%H%M%S%fZ")
    logs = ROOT / "evidence" / "runs" / stamp
    logs.mkdir(parents=True, exist_ok=False)
    record = {
        "scope": "Full MF-21 Target, manuscript smoothness, and component declarations",
        "started_utc": now.isoformat(),
        "limits": {"threads": 1, "memory_MiB": 4096},
        "comparator": "not_run",
        "github_run_id": None,
        "runner_sha256": sha(Path(__file__).resolve()),
        "runs": [],
        "source_hashes": {p: sha(ROOT / p) for p in MODULES},
        "pin_hashes": {p: sha(ROOT / p) for p in
                       ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]},
        "manuscript_sha256": sha(ROOT / "original-proof" / "solution.md"),
        "passed": False,
    }
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    record["package_heads"] = {}
    for package in manifest["packages"]:
        path = ROOT / manifest["packagesDir"] / package["name"]
        head = subprocess.check_output(
            ["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
        record["package_heads"][package["name"]] = head
        if head != package["rev"]:
            raise RuntimeError(f"Dependency pin mismatch: {package['name']}")
        dirty = subprocess.check_output(
            ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"],
            text=True).strip()
        if dirty:
            raise RuntimeError(f"Tracked dependency edits: {package['name']}")

    environment = dict(os.environ, LEAN_NUM_THREADS="1")
    lock_path = Path("/private/tmp/nla-lean-compiler.lock")
    with lock_path.open("a+") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise RuntimeError("Another cooperating local Lean runner holds the compiler lock")
        for source in MODULES:
            output = ROOT / ".lake/build/lib/lean" / Path(source).with_suffix(".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            log = logs / (Path(source).stem + ".log")
            command = ["lake", "env", "lean", "-j1", "-M4096", "-o",
                       str(output.relative_to(ROOT)), source]
            print("Running: LEAN_NUM_THREADS=1 " + " ".join(command), flush=True)
            with log.open("w") as handle:
                result = subprocess.run(command, cwd=ROOT, env=environment,
                                        stdout=handle, stderr=subprocess.STDOUT)
            run = {"source": source, "command": command,
                   "environment": {"LEAN_NUM_THREADS": "1"},
                   "exit_code": result.returncode,
                   "log": str(log.relative_to(ROOT)), "log_sha256": sha(log)}
            record["runs"].append(run)
            if result.returncode or sha(ROOT / source) != record["source_hashes"][source]:
                print(log.read_text(), end="")
                break
            run["output_sha256"] = sha(output)
        else:
            for source, digest in record["source_hashes"].items():
                if sha(ROOT / source) != digest:
                    raise RuntimeError(f"Source changed during compilation: {source}")
            for pin, digest in record["pin_hashes"].items():
                if sha(ROOT / pin) != digest:
                    raise RuntimeError(f"Dependency configuration changed during compilation: {pin}")
            audit = (logs / "Audit.log").read_text()
            reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", audit)
            expected = re.findall(r"^#print axioms (\S+)$",
                                  (ROOT / "Audit.lean").read_text(), re.MULTILINE)
            actual = [name for name, _ in reports]
            if len(expected) != len(set(expected)) or sorted(actual) != sorted(expected):
                raise RuntimeError(f"Axiom reports do not match Audit.lean: {actual}")
            record["axioms"] = {}
            for name, text in reports:
                axioms = {part.strip() for part in text.split(",") if part.strip()}
                record["axioms"][name] = sorted(axioms)
                if not axioms <= PERMITTED:
                    raise RuntimeError(f"Unpermitted axioms in {name}: {axioms - PERMITTED}")
            record["passed"] = True
        record["finished_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
        serialized = json.dumps(record, indent=2) + "\n"
        (logs / "record.json").write_text(serialized)
        (ROOT / "evidence" / "latest-local.json").write_text(serialized)
    print("PASS: full MF-21 local elaboration and axiom audit; Comparator is separate" if record["passed"] else "FAIL: see retained logs")
    return 0 if record["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())

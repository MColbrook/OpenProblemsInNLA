# MI-28 Lean formalization

This project formalizes the complete existing solution of MI-28. For every
integer $`n\ge1`$, complex positive definite matrices $`A,B`$, every real
$`k\ge0`$, and $`0\le p\le2`$, it proves

```math
\det(A^k+|AB|^p)\ge\det(A^k+A^pB^p),
\qquad |AB|=((AB)^*(AB))^{1/2}.
```

Both determinants are proved positive real, including the determinant of the
possibly non-Hermitian right matrix. Powers use spectral functional calculus;
zeroth powers of positive definite matrices are the identity. The stronger
normalized log-majorization is also proved for the full range. The target has
no commutativity, spectral-gap or entry-size assumption, and no upper bound on $`k`$. The
optional semidefinite extension in the analytic note is outside this canonical
positive-definite target.

The main declarations are `NLA.MI28.determinant_comparison` and
`NLA.MI28.full_log_majorization`. [IMPLEMENTATION-MAP.json](IMPLEMENTATION-MAP.json)
maps all 20 frozen contracts to their source declarations and hashes.
[PROOF-REVIEWER-MAP.md](PROOF-REVIEWER-MAP.md) explains the proof, endpoints and
unchanged MI24 reuse. [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) describes the
single fixed half-exponent certificate and its actual consumer.

## Current verification status

- **Actual local Lean: PASS.** Root's macOS local365 completion authenticates
  all 52 project proof modules: 8 freshly compiled in that run and 44 reused
  from source-matched successful local outputs. All 20 selected declarations
  passed their axiom and kernel-trust checks. Root used one compiler process,
  one thread and a 4096 MiB limit. The mixed run also contained unrelated MF14
  failures; the pass claim is specifically for the MI28 closure.
- **Actual local type/body diagnostics: PASS.** Local366 separately elaborated
  the challenge and solution; all 20 types and universes agree after erasing
  binder names only. The actual proof-body graph reaches the half certificate
  and both generated LeanCert integer checks from the final theorem.
- **Two independent nonauthor source reviews: PASS / APPROVE.** Each fresh
  reviewer read the complete target and 52-module closure, applying pinned
  Tau Ceti rubrics. Their Python evidence audits and root's subsequent audit
  replays are receipt checks, not additional Lean runs. See
  [REVIEW-INDEX.md](REVIEW-INDEX.md).
- **Fresh canonical entrypoint: PASS.** Direct local Lean compilation of
  `Solution.lean` passed with all20 axiom/trust reports. It reused51 authenticated
  dependency outputs under the same one-thread/4096 MiB limits; this was not a
  standalone Lake build. See the [actual receipt](verification/canonical-local/RECEIPT.json).
- **Independent publication-metadata review: PASS.** The nonauthor reviewer
  authenticated the exact package, evidence relocations, schema, links and
  privacy. The [review](reviews/package-referee2/MANIFEST.json) is separate
  from both full proof-source reviews and from Lean execution.
- **Standalone Lake build and final non-root Linux GitHub
  Comparator/default-kernel/sandbox/negative controls: pending.** The GitHub
  checks are **NOT RUN**. Neither accepted count is increased here.

Exact hashes, origins and limitations are recorded in [STATE.json](STATE.json)
and the integrated verification evidence. The metadata is a schema-v0.4
self-report, [formalization.yaml](formalization.yaml), serialized in JSON syntax
(valid YAML). Schema validation does not execute Lean or prove fidelity.

## Reproduction and package layout

The standalone package pins Lean `v4.33.1`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`. The entire dependency lock is retained.
From the assembled `matrix-inequalities-and-norms/MI-28/lean` directory, with
the pinned dependencies available, the ordinary proof build is:

```sh
lake build Solution
```

The default `lake build` now also selects `Solution`. These are reproduction
instructions, not commands executed by this documentation task. The original
local evidence comes from root's serial direct-Lean runner. It compiled the
identical aggregate bytes as `NLA/MI28/Solution.lean`; the publication path is
`Solution.lean`. [LAKE-CONFIGURATION.json](LAKE-CONFIGURATION.json) binds that
mapping and the only two configuration corrections: the default target and the
root manifest name `NLAMI28`. No dependency revision changes.

`Challenge.lean` intentionally contains the 20 trusted statement placeholders;
it is not imported by `Solution`. The frozen challenge, definitions and
`comparator.json` remain byte-identical to the statement-first local350 gate.
Comparator must run in its genuine separate non-root Linux environment using
the pinned comparator contract; an ordinary Lake build or local type dump is
not that check. Exact tested commit and run details must be added after the
actual GitHub execution.

**Historical records:** the frozen source comments saying “UNELABORATED” or
that no implementation exists describe the earlier statement draft. They are
retained to preserve the freeze. The old `IMPLEMENTATION-PLAN.md`, old
`NUMERICAL_TARGETS.md` and original Lake configurations are archived under
`history/statement-draft/`. This README, current maps and `STATE.json` describe
the completed proof. The retained canonical solution's pre-Lean verification
footer likewise describes its original September 11 publication.

This directory contains the unchanged reviewed proof sources and retained
execution evidence. The original documentation draft and its environment-bound
integrity checker are preserved in `verification/history/`; that checker is
historical provenance, not a portable Lean command. See
[verification/README.md](verification/README.md) for the retained commands,
source hashes, local diagnostic records and review scopes.

## Attribution and public scope

George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, contributed the full analytic solution and
this formalization with substantial ChatGPT/Codex assistance. Prior problem and
large-base work by Ghabries, Abbas, Mourad and Assi, the Furuta/Fujii/Tanahashi
background, and all unchanged MI24 and earlier code credits are preserved in
[SOURCE-ATTRIBUTION.json](SOURCE-ATTRIBUTION.json). The proof author also wrote
these docs; the two final source referees are different agents. Their review
is not external human peer review or official Tau Ceti engine execution.

The recorded upstream main is
`9342b3d80c207d3e0bfd61251334d027935c387c`. MI-28 was already **Solved** by the
solution merged in PR #85. This contribution is a formalization, not a new
mathematical resolution. Root's targeted PR refresh and subsequent dated audit
of 15 visible public repositories, 271 branch heads and 225 complete immutable
trees found no MI28 formalization within their ID/path scope. The 17 matching
commits only archive the same canonical README. This does not cover private,
deleted, unpublished or differently named work, nor continuously updated heads.
See [PUBLIC-SCOPE.json](PUBLIC-SCOPE.json) for scope and the partial-audit
resumption history. This docs task performed no network or Git operations.

The [coordinator publication preflight](verification/MI28-ROOT-PACKAGE-PREFLIGHT.json) passed2131 package/schema/identity/privacy checks. All mathematical source, frozen statement and dependency-pin bytes remain unchanged.

# MF-21 formalization

This is the complete source development for all three assertions of
Conjecture 8.4 of Barrera–Böttcher–Grudsky–Maximenko, for every integer
`m ≥ 3`, together with the revised manuscript's stronger continuous-family
obstruction and sharp maximum-error bounds.

The development capstones have passed Lean 4.33.1 with `--trust=0` and only
the standard foundational axioms. **Canonical package verification is still
in progress:** a local build does not replace the required independent
statement reviews and fresh non-root Linux Comparator run. No publication
or push has been authorized.

## Entry points

- [`MF21/Definitions.lean`](MF21/Definitions.lean): actual matrix, ordered
  eigenvalues, source grid, remainder and exact target quantifiers.
- [`Challenge.lean`](Challenge.lean): five specification obligations, with
  deliberate placeholders only in this trusted, separate environment.
- [`Solution.lean`](Solution.lean): five proved exports; does not import
  Challenge.
- [`MF21/FinalTarget.lean`](MF21/FinalTarget.lean): assembly of the complete
  analytic proof, including the same smooth family and sharpness bounds.
- [`NUMERICAL_TARGETS.md`](NUMERICAL_TARGETS.md): statement correspondence,
  intermediate proof map and acceptance requirements.
- [`comparator.json`](comparator.json): all advertised exports and the exact
  permitted axiom set, without replaceable definition holes.

## Reproduction

Use the committed toolchain and dependency manifest:

```sh
lake exe cache get
lake build Solution
```

The optional [`replay_development.py`](replay_development.py) compiles every
local proof source with `--trust=0` into an initially empty output directory,
then audits the transitive axioms of every local declaration. It takes
explicit toolchain and external dependency-cache paths; it does not use
existing project oleans:

```sh
python3 replay_development.py \
  --lean /absolute/path/to/lean \
  --packages /absolute/path/to/external/.lake/packages \
  --output /absolute/path/to/new-replay-directory \
  --exclude Challenge --jobs 2
```

Challenge is compiled separately because its specification placeholders
are intentional and must not enter the solution's proof closure.

The authoritative repository check requires a committed project and the
isolated Linux prerequisites in [`tools/lean/HARNESS.md`](../../../tools/lean/HARNESS.md):

```sh
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh matrix-functions-and-stability/MF-21/lean \
  /absolute/path/to/nla-lean-tools
```

## Sources and attribution

The conjecture is due to Mauricio Barrera, Albrecht Böttcher, Sergei Grudsky
and Egor Maximenko. The original manuscript is by George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology. The simple-loop method and related local expansions retain the
attribution given in the revised manuscript, including Bogoya–Grudsky (2025).

This formalization and the September 2026 proof revisions were produced by
OpenAI Codex AI agents in response to the maintainer's request. Reports
identify authorship and independent review separately. No human peer review,
source-author endorsement, priority claim or official Tau Ceti review is
asserted.

Mathlib is pinned at `0df444a360eaa60ab8c11dca51a86af692955474`.
The six-file proof of transcendence of π is adapted from Trevor Morris's
`lean-formalizations` at `3a24a73416f83c32b4d4a2ac09588524c6291650`;
its [provenance](MF21/MF21Transcendence/provenance.json),
[source disclosures](MF21/MF21Transcendence/README.md) and
[Apache-2.0 license](MF21/MF21Transcendence/LICENSE) are retained.
No result from the mathematical literature is introduced as a custom axiom.

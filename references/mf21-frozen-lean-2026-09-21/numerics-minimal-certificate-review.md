# MF-21 minimal numerical certificate review

Reviewer: `mf21_restart_lean_audit`; candidate author: `mf21_restart_manuscript`. **APPROVE** for the exact candidate below, its unchanged statement, and its kernel-only certificate design. This reviewer ran no Lean compiler, Lake build, or Comparator. This report does not assert that the revised whole project or Linux Comparator has passed.

## Exact reviewed inputs

| Input | SHA256 |
|---|---|
| `/private/tmp/MF21NumericsCandidate.lean` | `c4677460fab467e2992c9fd0b1d74abf0d682ba8a7c89857d77e2b481a89e410` |
| Prior `/private/tmp/MF21NumericsCandidate_STATEMENTS.md` | `ac95aa3b3aee13f8c14ecac1cb15914d98efc0c5c2a91c0babafe2fc7e71b0f9` |
| Original published `MF21Restart/Numerics.lean` | `9d8eb86229773759393cecd14b2651dfc6a994c270dc1ee82d3131c1af60bc42` |
| Pinned `LeanCert/Core/IntervalRat/Transcendental.lean` | `3968b194323b625283fae2c53900340ff13ec6eaf7d52e958e5c83246f580272` |
| Pinned `LeanCert/Tactic/Verification.lean` | `2c576708b528acdde17796b0b715b83079f9cad377182dbd87c248323ff0a58c` |

The LeanCert checkout and dependency manifest both name commit `621a43d7cf21f87872392a01e874f2f1dbddc926`. Neither inspected library file has a working-tree modification. The Mathlib pin remains `0df444a360eaa60ab8c11dca51a86af692955474`.

## Statement and mathematical proof

Candidate line 19 has the exact original exported type, including strictness and normalization:

```lean
theorem MF21Restart.phase_window_margin :
    (1 / 4 : ℝ) < Real.sin (Real.pi / 4)
```

A direct signature comparison with the original Numerics source found no change. This is also the unchanged Challenge/Solution contract. The candidate adds no parameter, hypothesis, premise, typeclass assumption, or replacement definition. It preserves the numerical scope selected before proof in `STATEMENTS.md:88–93`: one closed square-root residual, used for the phase-window margin.

At lines 21–23 the certificate is the closed rational equality
`sqrtRatLowerPrec (2 : ℚ) 0 = 1`. In the pinned implementation, `intSqrtNat` is `Nat.sqrt` (`Transcendental.lean:172–174`), and the lower enclosure is explicitly defined at lines 220–230. For `q = 2` and scale zero, its numerator and denominator are 2 and 1, its scale factors are 1, and the result is `Nat.sqrt 2 / 1 = 1`. Zero is the smallest admissible natural scale; the default scale 20 is not used. No search, interval subdivision, Taylor expansion, eigenvalue evaluation, or numerical integration is introduced.

The certificate is mathematically essential to the source proof. Lines 25–27 apply the actual proved theorem `sqrtRatLowerPrec_le_sqrt`, whose complete statement at `Transcendental.lean:400–401` is

```lean
{q : ℚ} → 0 ≤ q → (k : ℕ) →
  (sqrtRatLowerPrec q k : ℝ) ≤ Real.sqrt q
```

The rational nonnegativity premise is discharged at the exact value 2 by `norm_num`; it is not assumed. The proof rewrites the enclosure by `hcert` to obtain exactly `1 ≤ Real.sqrt (2 : ℝ)`. The pinned soundness proof at lines 402–467 derives its enclosure from `Nat.sqrt_le'`, positive denominator/scale factors, and ordinary real square-root inequalities; it is a theorem, not a literature axiom or an assumed numerical bound.

Finally the same exact identity `Real.sin_pi_div_four` and `linarith only [hs]` show `1/4 < sqrt 2 / 2`. The stronger intermediate lower bound `sqrt 2 / 2 ≥ 1/2` makes the strict margin valid. The LeanCert computation is used in this chain, rather than attached as an unrelated check to a separate proof of the target.

## Trust and computational scope

Candidate line 15 fixes `leancert.trust` to `"kernel"`. The selected low-level certificate tactic is defined in the pinned `Verification.lean:550–555`; it obtains the current verification configuration and checks the actual certificate goal. Source inspection establishes:

- `parseCertificateGoal` at lines 267–294 requires a closed decidable proposition, rejecting unresolved metavariables, loose variables, and free variables. This candidate's rational equality meets that scope.
- `closeKernelTypedCore` at lines 328–345 constructs a decision proof and registers it through `mkAuxLemma` with asynchronous elaboration disabled, for eager kernel checking. It does not create a proof axiom.
- The explicit kernel route at lines 501–511 either returns that proof or fails. The native and automatic routes are separate branches; kernel mode has no native fallback.
- Candidate line 30 executes `#assert_trust kernel phase_window_margin`. The command at lines 632–660 collects the theorem's transitive axioms and rejects native-compiler, `sorryAx`, and custom dependencies. Only `propext`, `Classical.choice`, and `Quot.sound` are classified as foundational at lines 614–626.

The candidate contains no `sorry`, `admit`, custom axiom, `unsafe` declaration, or `native_decide`. Although the verifier module imports native-verification machinery to implement other modes, the chosen branch and resulting theorem's transitive axiom check exclude that trust from this proof. The low-level tactic is an implementation interface at this exact pinned revision; its use is transparent in the statement lock and this review.

The five explicit imports replace the broad `LeanCert.Tactic` import. The certificate itself has fixed scale zero and a tiny integer square-root input. These are source-level reductions in computational scope, not a measurement of Linux peak memory or a diagnosis of the original exception. No compiler limit or dependency revision is increased.

## Actual local candidate evidence

The coordinator's retained `evidence/logs/numerics-minimal-candidate-02.json` has SHA256 `80cf97c5c8d989c454d98f2970e0c7a77fa0f2ecccf9e5d7dc58c4d77e38f987`. The reviewer independently matched its source hash to the candidate and its log hash to `evidence/logs/numerics-minimal-candidate-02.log`, SHA256 `cf12e33044415f5b0f465b37eda09124ec5693822d32ad0bb328bce7241777be`.

That actual local command used `lake env lean -j1 -M4096 -R /private/tmp`, the exact candidate source, and `-o`, `-i`, `-c`, and `--json`, with `LEAN_NUM_THREADS=1`. It ran from `2026-09-21T00:55:49.026591Z` to `00:56:01.474481Z` and exited 0. Consequently the in-source trust assertion completed. The only printed theorem-axiom report is exactly:

```text
'MF21Restart.phase_window_margin' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

The prior candidate-01 attempt is retained as a failed input-root invocation; candidate-02 corrects the command's source-root argument without changing source bytes. The successful command above is a direct local Lean invocation with info/code emission. It is not the fresh Linux Lake `--setup`/Comparator invocation, and it does not establish that the original Linux memory exception has been eliminated there.

The candidate is approved for an unchanged-byte copy into the project, followed by the coordinator's full serial rebuild binding the new Numerics and Lakefile hashes. The old 125-source success applies to the old Numerics implementation and original Lakefile; it must remain historical evidence. A later repaired publication and Linux result require their own receipts. This component repair changes no mathematical target, contract count, authorship, or distinct-problem count.

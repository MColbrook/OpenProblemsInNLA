# Independent fixed-index proof and numerical review

Date: 20 September 2026.
Reviewer: /root/mf21_restart_manuscript.
Verdict: **APPROVE**, limited to the intermediate declarations identified below.
No material mathematical, source-fidelity, or numerical-scope issue was found.

This report applies the proof-quality and numerical-certification portions of
/Users/georgestepaniants/Research/project/lean-verification/REFEREE_STANDARDS.md,
SHA-256 e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1.
It is not an approval of the full MF-21 target, a Comparator review, or a
GitHub sandbox check.

## Frozen sources and review scope

All paths below are relative to the MF21-restart project root unless stated
otherwise. I read the complete final versions of both proof files, their
source-matched local logs, Definitions.lean, and STATEMENTS.md. I did not
compile, run LeanCert, or change any Lean source.

| File | SHA-256 |
| --- | --- |
| MF21Restart/FixedIndex.lean | da98fb1baae1b4b1736f5be8f03261b4a609182342df6158ac2394713313fc28 |
| MF21Restart/Numerics.lean | 9d8eb86229773759393cecd14b2651dfc6a994c270dc1ee82d3131c1af60bc42 |
| MF21Restart/Definitions.lean | 35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51 |
| STATEMENTS.md | 6709fd19a3765c83ce16986780963e1f22ae49472b5ea7f013e968f37ab27691 |

The manuscript remains the source at commit
eb37bc17a462177f57efa270e9a9f9b17e9d88e2, SHA-256
6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa.
The relevant source is equation (30), including the preceding contradiction
hypothesis and the full Taylor expansion, and Lemma 4's phase-window margin.

Reviewed public results:

* MF21Restart.implicit_phase_ratio_limit.
* MF21Restart.symbol_scaled_limit.
* MF21Restart.fixed_index_limit_of_implicit_phase.
* MF21Restart.critical_bound_implies_fixed_index_limit.
* MF21Restart.phase_window_margin.

I also checked the helper MF21Restart.two_mul_sin_half.

## Analytic proof review

In FixedIndex.lean, lines 19–24 prove the identity
2 sin(y/2)=y sinc(y/2), explicitly handling y=0. The definition and continuity
of sinc are reused from the pinned Mathlib Sinc.lean; no new analytic axiom
or independently defined replacement for sinc is introduced.

Theorem implicit_phase_ratio_limit, lines 28–40, divides the actual eventual
implicit equation by h and uses continuity of eta at zero. Its conclusion
is derived from that equation, not assumed. The eventual positivity of h
supplies the required nonzero denominator. The proof deliberately rewrites
only the numerator by congrArg before cancelling, so it preserves eta(y_n).
No assumption h_n->0 is needed for this first implication.

Theorem symbol_scaled_limit, lines 44–59, uses the exact identity

    symbol(m,y_n) / h_n^(2m)
      = ((y_n/h_n) sinc(y_n/2))^(2m).

The sinc factor tends to 1, giving the claimed power limit. The absence of
a nonzero-h hypothesis is correct under Lean's totalized field division:
the displayed algebraic identity remains valid when h_n=0. The m=0 case
also remains valid, since the exponent is zero and both sides are 1.
No artificial m>=3 restriction is needed for this elementary ingredient.

Theorem fixed_index_limit_of_implicit_phase, lines 63–93, derives the symbol
limit from the previous two results. It divides the absolute error by the
positive h_n^(2m), bounds the normalized error by C h_n, and applies the
existing squeeze_zero_norm' theorem. Adding that error to the symbol limit
gives the required limit for ev_n. The exponent drops from 2m+1 to 1
exactly once. There is no extra endpoint term or omitted coefficient.

An explicit C>=0 hypothesis is unnecessary: the eventual absolute-value
bound together with h_n>0 already forces a nonnegative right-hand side.
The squeeze theorem needs the eventual norm bound and convergence of the
bound to zero, both of which are supplied. Negative C does not create an
unsound cancellation.

The near-zero hypothesis y_n->0 is substantive, rather than redundant.
For example, eta(t)=t^2, b=0, h_n=1/(n+1), and y_n=n+1 satisfy the implicit
equation with positive h_n->0, but y_n/h_n diverges. Thus the proof correctly
retains the hypothesis selecting the near-zero branch.

The generic hypotheses are also nonvacuous: for constant eta=alpha, take
h_n=1/(n+2), y_n=(b+alpha)h_n, and ev_n=symbol(m,y_n), with C=0. These satisfy
the hypotheses and produce the asserted limit.

## Connection to the actual eigenvalues and equation (30)

Theorem critical_bound_implies_fixed_index_limit, lines 100–136, uses the
actual eigenvalue function from Definitions.lean. It combines:

1. The hypothetical all-index UniformBound at p=2m.
2. The Taylor estimate for the same expansion d (2*m).
3. The near-zero implicit phase relation and continuity.

Lines 123–131 require both n>=N and n>=j eventually before applying the
uniform eigenvalue bound. Together with hj, this keeps the published index
in 1,...,n and prevents use of the totalized out-of-range eigenvalue.
The triangle inequality yields the correct combined constant C+B.

Both error estimates contain the identical sum through k=2m, including
d_(2m). It cancels in the subtraction. The conclusion therefore has limit
(pi*j+eta(0))^(2m), with no subtraction of eta(0)^(2m).
The scale (n+2)^(2m) times the eigenvalue is exactly h^(-2m).

After supplying eta(0)=(m-1)pi/2, this is the manuscript's equation (30).
For the actual contradiction argument, m>=3 and j>=1 further imply that
this limit is positive, a fact needed later for reciprocals. That later
reciprocal step is not asserted by these declarations.

This theorem does not prove the critical uniform bound; it uses the
assumption made for contradiction in the manuscript. Nor does it prove
the concrete implicit-phase construction or its Taylor estimate.
Those obligations remain explicit hypotheses, and the module documentation
and STATEMENTS.md correctly disclose that scope. The theorem is a valid
intermediate implication, not a proof of MF21Restart.Target.

## Numerical target and trust review

Numerics.lean, lines 15–20, proves exactly the selected inequality
1/4 < sin(pi/4). It first uses Mathlib's exact sin_pi_div_four identity.
The only certificate then proves the sufficient closed bound
1<=sqrt(2); an exact cast and linear arithmetic give the strict final
margin. This is a sound weakening of the numerical subgoal: sqrt(2)/2
is at least 1/2, which exceeds 1/4.

There are no variable interval boxes, matrix-size enumerations, domain
subdivisions, or Taylor-depth parameters. The trigonometric evaluation is
removed symbolically before the single algebraic certificate. I found no
gratuitous computational search or repeated certificate.

The inequality is the positive margin needed at the phase-window
endpoints after the exact periodicity/sign reductions in Lemma 4.
It also supplies a sufficient scalar margin for the derivative comparison
once the analytic derivative bounds are proved. It does not itself prove
the perturbation estimates, determinant equivalence, or root uniqueness.

Kernel mode is requested globally at line 11 and explicitly on the
interval_decide call at line 18. I inspected the pinned LeanCert
Verification.lean: its kernel branch uses the kernel-only certificate
closure and does not fall back to the native branch on failure.
The final local axiom output, described below, is consistent with this
choice and contains no native-decide axiom.

The source contains no sorry, admit, custom proof axiom, unsafe shortcut,
or replacement definition hiding one of the analytic conclusions.
Standard symbolic and limit lemmas are reused. The small sinc identity
helper remains in the proof module, not the trusted Definitions.lean file.

## Local evidence, distinguished from independent compilation

The coordinator reported successful local exits (exit code 0) for the
following actual commands, executed from the MF21-restart project root:

    env LEAN_NUM_THREADS=1 lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/FixedIndex.olean MF21Restart/FixedIndex.lean
    env LEAN_NUM_THREADS=1 lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/Numerics.olean MF21Restart/Numerics.lean

I independently read and hashed the resulting source-matched logs.
The exit-code reports are the coordinator's execution evidence; I did
not rerun either command.

| Evidence | SHA-256 |
| --- | --- |
| evidence/logs/fixed-index-05.log | dd5e18e30f671812922fc80e2f0b8bb43c92e79e653b213dfb3ad90201d1eb17 |
| evidence/logs/numerics-03.log | 81b0aa4a269aa86bcf2d56c963b7e8cc080ba96b3189d5537e1d44f7d5e4f702 |
| .lake/build/lib/lean/MF21Restart/FixedIndex.olean | 69a19f40e98e9902832c3d483e5d2815a469c7aa78dff5d666c1d4b955361889 |
| .lake/build/lib/lean/MF21Restart/Numerics.olean | 3aff4ea6140a0533a7b96635b48d601eca2c614490e38c866cff3c6810d56445 |

The FixedIndex log lists all four analytic theorem declarations and the
Numerics log lists phase_window_margin. Each reports precisely:

    [propext, Classical.choice, Quot.sound]

No sorryAx, native-decide axiom, or custom axiom appears in these outputs.
This is local Lean evidence, not GitHub Comparator/kernel/sandbox evidence.

The toolchain file specifies leanprover/lean4:v4.33.1. The installed
dependency checkouts match the manifest and were clean under git status:

* LeanCert: 621a43d7cf21f87872392a01e874f2f1dbddc926.
* Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474.

No GitHub or Comparator run was performed for this review.
GitHub run IDs: none.

## Acceptance boundary

Approve the five intermediate declarations at the recorded hashes for
their stated scope. There are no material change requests.

The root construction, determinant estimates, indexing, concrete Taylor
family, trace limit, and trace contradiction remain separate obligations.
This report does not establish the full canonical target or verify the
whole manuscript. It increases neither the count of complete distinct
Lean verifications nor the count of new mathematical resolutions.

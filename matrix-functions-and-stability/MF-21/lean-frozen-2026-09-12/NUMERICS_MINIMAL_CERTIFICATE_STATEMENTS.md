# MF-21 numerical certificate candidate: statement lock

This candidate changes only the implementation of the already locked numerical
certificate. It does not change the manuscript or the canonical Numerics source.

The sole real numerical residual remains exactly `1 ≤ Real.sqrt (2 : ℝ)`.
The exported theorem remains exactly:

```lean
theorem MF21Restart.phase_window_margin :
    (1 / 4 : ℝ) < Real.sin (Real.pi / 4)
```

Use the pinned LeanCert rational square-root lower enclosure
`LeanCert.Core.IntervalRat.sqrtRatLowerPrec (2 : ℚ) 0`, with the scale parameter
explicitly fixed to zero. Its computation is `Nat.sqrt 2 / 1 = 1`. Certify the
closed rational equality to `1` using LeanCert's `leancert_verify_cert` with
`set_option leancert.trust "kernel"`. Apply LeanCert's proved soundness theorem
`sqrtRatLowerPrec_le_sqrt` at the same scale to establish the real residual.
Use the unchanged exact identity `Real.sin_pi_div_four` and linear arithmetic
to establish the exported strict margin.

No numerical parameter is searched, no variable interval is subdivided, and no
numerical eigenvalue or integration calculation is introduced. Keep both
`#assert_trust kernel phase_window_margin` and `#print axioms phase_window_margin`.
Do not raise the one-thread, 4096 MiB compilation limit or introduce native trust.

Implementation rationale, based on pinned source inspection:

- `LeanCert.Tactic.IntervalAuto.PointIneq` exposes a Taylor-depth argument on
  `interval_decide`, not a user-facing dyadic-precision argument.
- `LeanCert.Core.IntervalDyadic.sqrt` uses the conservative lower endpoint zero,
  so its dyadic bound alone cannot prove the positive lower bound required here.
- `LeanCert.Core.IntervalRat.Transcendental` defines the explicitly parameterized
  rational enclosure and proves its soundness for every natural scale. The
  default scale is 20, but the exact required lower bound already holds at zero.
- `LeanCert.Tactic.Verification` defines the kernel certificate choke point and
  trust audit. The certificate proof is used essentially through the square-root
  soundness theorem; it is not an unrelated check attached to an independent proof.

The candidate imports these two specific LeanCert modules, rather than the
umbrella `LeanCert.Tactic`, plus the specific Mathlib trigonometric and arithmetic
tactic modules. This reduces unnecessary evaluator/tactic initialization. It is
an implementation proposal, not yet compiled or measured by this reviewer.

Pinned LeanCert commit: `621a43d7cf21f87872392a01e874f2f1dbddc926`.
Relevant exact source locations: `Core/IntervalRat/Transcendental.lean:215–231`
(scale and enclosure), `:399–401` (soundness), and
`Tactic/Verification.lean:267–291,328–352,550–555,632–660`
(closed certificate validation, kernel checking, tactic, and trust audit).

Observed verification context: the original source passed the retained local
125-module run and a later local Lake-shaped invocation reported by the
coordinator. GitHub run `35548010081` failed, including an interpreter memory
exception while building the original Numerics module with `-M4096` and a
separate missing vendored module caused by the Lake registration. This proposal
does not claim to have established the memory cause or passed Linux/Comparator.

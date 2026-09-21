# Referee B: the actual high-phase remainder bound

Verdict: **APPROVE**, scoped to
`MF21Restart.manuscriptError_high_phase_small` in
`MF21Restart/SpectralWindowBounds.lean`. The reviewer did not author this
module, run a compiler, or edit its source. This is a review of a partial
ingredient, not a claim that Lemma 4, MF-21, or Comparator is complete.

## Frozen files and observed evidence

| Item | SHA-256 |
| --- | --- |
| `MF21Restart/SpectralWindowBounds.lean` | `4e188878d1a1b079f0569bd010bfa88f7b151ea690453d7efb8500789ca9efd3` |
| `SPECTRAL_WINDOW_BOUNDS_STATEMENTS.md` | `3c6ac1b5f7233f263e62d964eb022464d5056033f5fac770105c6557d61a3945` |
| `evidence/logs/spectral-window-bounds-01.json` | `b2905684de66525c4271e3f56a702c88919b95c98d4b9aeb730744afdbd542c3` |
| `evidence/logs/spectral-window-bounds-01.log` | `9f3e6360135837232ff2d60e717a61268a532df3cc257ff3e36e5a8bff4a94c5` |
| `.lake/build/lib/lean/MF21Restart/SpectralWindowBounds.olean` | `44d822e6cac370ecf3de9a4b3411307c0b6db6ee8e3ca8cb0e41fec8cb25748c` |

The reviewer recomputed the source, log, and output hashes and matched
them to the retained JSON. That record reports source unchanged,
`exit_code: 0`, `LEAN_NUM_THREADS=1`, and the command

```
lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/SpectralWindowBounds.olean MF21Restart/SpectralWindowBounds.lean
```

The observed log prints the stated theorem with only `propext`,
`Classical.choice`, and `Quot.sound`. This is local development evidence;
no GitHub Comparator result is claimed.

The original manuscript hash is
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`;
the pinned referee rubric hash is
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Mathematical review

The exact source is the first quantitative paragraph of Lemma 4,
manuscript line 237. The integer `J` is selected after `m` and before
both `n` and `θ`, and the statement uses the existing actual phase and
remainder. No smallness estimate is included as a premise.

The private lemma at lines 9–28 chooses
`L = max 0 (log (8*C)/c) + 1`. Both the logarithm argument and the
divisor are positive. Thus `log (8*C) < c*L`, which proves the strict
estimate `C*exp(-c*L) < 1/8`. There is no numerical approximation or
finite-grid check.

At lines 40–45, the integer threshold satisfies
`J*pi > L+B+9*pi/4`. The identity
`n*θ = F_n(θ)+eta(θ)-2*θ`, the lower bound `eta(θ) >= -B`, and
`θ <= pi` consequently give `n*θ >= L` throughout the declared phase
range. The constant `9*pi/4` includes both the phase-window displacement
`pi/4` and the full `2*pi` loss from `2*θ`; neither loss is omitted.
Multiplication by `-c` correctly reverses the inequality.

At lines 57–68 the actual exponential estimates then give
`|E| < 1/8 < 1/4` and
`|E'| < (n+1)/8 < (n+2)/8`. Strictness of the derivative bound uses the
positive factor `n+1`. The natural-number and real-number casts have the
intended meanings. Both endpoints of the closed theta interval are
included. The stronger quantification over every `n` is valid; for small
`n` the high-phase premise may be empty, and the proof never assumes
that it is nonempty.

No material issue was found. The unused `Numerics` import and unused
positivity witnesses are optional cleanup only. This result supplies
smallness on a whole range; root existence, derivative sign on each
cell, exclusion of the last artificial-root cell, and downward index
counting remain separate obligations. The imported actual error bounds
were reviewed separately; this report does not re-review the reviewer's
own upstream coefficient and phase-zero modules.

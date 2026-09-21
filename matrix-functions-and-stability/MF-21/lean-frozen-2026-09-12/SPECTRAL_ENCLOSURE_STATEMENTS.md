# Statement lock: strict spectral enclosure of the actual Toeplitz matrix

Locked before writing `MF21Restart/SpectralEnclosure.lean` on 20 September
2026. The actual integral `fourierCoeff`, `toeplitz`, sorted eigenvalue
list and published one-based accessor remain unchanged.

For every natural m,n with `1 <= m`, prove:

```lean
theorem toeplitz_posDef (m n : ℕ) (hm : 1 ≤ m) :
    (toeplitz m n).PosDef

theorem toeplitz_upper_complement_posDef (m n : ℕ) (hm : 1 ≤ m) :
    (((4 : ℝ) ^ m) • (1 : Matrix (Fin n) (Fin n) ℝ) -
      toeplitz m n).PosDef

theorem eigenvalue_strict_spectral_enclosure
    (m n j : ℕ) (hm : 1 ≤ m) (hj : 1 ≤ j) (hjn : j ≤ n) :
    0 < eigenvalue m n j ∧ eigenvalue m n j < (4 : ℝ) ^ m
```

The positive-definite statements may include n=0, where the nonzero-vector
condition is vacuous; the eigenvalue statement's actual index hypotheses
force n positive. This harmless generality avoids an unnecessary dimension
premise. It does not count the totalized out-of-range accessor value.

Follow manuscript line 219: for a nonzero real vector v, expand the squared
modulus of its finite trigonometric polynomial and identify the weighted
integral exactly with the Fourier Toeplitz quadratic form. A real
representation `(sum v_j*cos(j*theta))^2 + (sum v_j*sin(j*theta))^2`
is permissible because it is exactly that squared modulus. Derive the
unweighted positive integral from the actual m=0 Fourier identity, or
equivalently Fourier orthogonality. Prove the weights `symbol m theta`
and `4^m-symbol m theta` are nonnegative on the interval and positive
except at the finitely many appropriate points. Continuity, almost-
everywhere positivity, and the nonzero unweighted integral must supply
strict weighted positivity. No nonzero-polynomial or spectral enclosure
premise may be assumed.

Reuse the pinned interval integral positivity / finite-sum identities and
`Matrix.PosDef` eigenvalue facts. In particular, matrix Hermitianity and
the exact scalar shift for the upper bound must be proved for the actual
matrix, not an unrelated discretization. No sampling argument, numerical
certificate, new axiom, or imported assertion of the desired positivity
is authorized.

Private finite-sum and strict weighted-integral helpers are permitted.
This component establishes the spectral prerequisite to Lemma 4; it does
not establish eigenvalue indexing, the implicit expansion, or the full
Target. The source author runs no Lean compiler; coordinator local serial
tests and any final GitHub Comparator checks must be reported separately.

# Upper endpoint phase: statement lock

With the actual definitions from PhaseZero, prove `manuscriptPsi m π = 0`
and `manuscriptEta m π = π` for `1 ≤ m`. For every `1 ≤ ell < m`, the
individual phase at π is `arg(1+r_ell(π))`. The roots indexed by ell and
m−ell are conjugate, and `Re(1+r_ell(π))>0` since `norm(r_ell(π))<1`.
Hence the two individual arguments are negatives, with no branch ambiguity.

Use the exact permutation `Fin.revPerm` of the m−1 stable indices to show
the finite sum equals its own negative. This also includes the real root
when m is even, and the empty sum when m=1.

This is the upper endpoint assertion in manuscript (7). It does not assert
that the argument of the product equals the sum of these arguments.

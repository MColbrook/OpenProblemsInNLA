# Weighted binomial identity: statement lock and exact proof

Locked before writing `MF21Restart/WeightedBinomialInverse.lean`,
20 September 2026. This is symbolic infrastructure toward the known
Duduchava–Roch inverse formula, not a new inverse-formula discovery, a
proof of the uniform kernel limit, or a completed MF-21 Target.

The coordinator authorized this bounded component after the telescoping
certificate below was derived and its signs and endpoints checked.
No manuscript changes or compiler processes are authorized here.

## Exact statements

Use Mathlib's ascending Pochhammer polynomial for real arguments. In this
document `(x)_a = (ascPochhammer ℝ a).eval x` means the ordinary polynomial
`x(x+1)...(x+a-1)`. In particular, subtraction in `(x-r)_a` is real
subtraction, not truncated natural subtraction.

Define

```lean
def weightedBinomialRisingSum (m d : ℕ) (x : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (m - d + 1),
    (m.choose r : ℝ) * (m.choose (d + r) : ℝ) *
      (ascPochhammer ℝ (2 * m)).eval (x - (r : ℝ))
```

The primary polynomial identity is

```lean
theorem weightedBinomialRisingSum_eq (m d : ℕ)
    (hm : 1 ≤ m) (hd : d ≤ m) (x : ℝ) :
    weightedBinomialRisingSum m d x =
      ((2 * m).choose (m + d) : ℝ) *
        (ascPochhammer ℝ m).eval x *
        (ascPochhammer ℝ m).eval (x + (d : ℝ))
```

Expose the division-free recurrence, with d<=m and every real x:

```text
x(x+d) S(x+1) = (x+m)(x+m+d) S(x).
```

Also prove the exact one-based finite-sum identity in real casts of natural
ascending factorials, allowing every natural offset d:

```lean
theorem weightedBinomialInverse_identity (m d j : ℕ)
    (hm : 1 ≤ m) (hj : 1 ≤ j) :
    (∑ k ∈ Finset.Icc 1 j,
      (m.choose (j + d - k) : ℝ) * (m.choose (j - k) : ℝ) *
        (k.ascFactorial (2 * m) : ℝ)) =
      (j.ascFactorial m : ℝ) * ((j + d).ascFactorial m : ℝ) *
        ((2 * m).choose (m + d) : ℝ)
```

This is the displayed sum in `INVERSE_KERNEL_RESEARCH.md` with i=j+d.
The symmetric case i<j follows by exchanging i and j and binomial symmetry;
it is not encoded using an invalid unguarded natural subtraction in a
possibly negative binomial lower index. No finite matrix inverse, Toeplitz
coefficient identification, or kernel limit is asserted by this component.

## Division-free telescoping proof

Fix d<=m, put N=m-d, `P(x)=(x)_(2m)` and
`w_r=choose(m,r)*choose(m,d+r)`. Let

```text
S(x) = sum_{r=0}^N w_r P(x-r),
G_x(r) = -r(d+r) w_r P(x+1-r).
```

The ordinary binomial recursion gives, for 0<=r<=N,

```text
(r+1)(d+r+1) w_(r+1) = (m-r)(m-d-r) w_r.                 (A)
```

Both sides are zero at r=N, including d=0 when r=m: the next binomial
coefficient is out of range. The Pochhammer identity

```text
y P(y+1) = (y+2m) P(y)                                  (B)
```

is a polynomial identity and remains valid at all zero or negative y.
Combining (A) and (B) gives the exact certificate

```text
x(x+d) w_r P(x+1-r)
  - (x+m)(x+m+d) w_r P(x-r)
    = G_x(r+1) - G_x(r).                                (C)
```

For an explicit sign check, subtract the right side of (C) from its left.
The result is `(x+r+d)w_r` times the left-minus-right side of (B), with
y=x-r, plus `P(x-r)` times the left-minus-right side of (A). The two
coefficient identities are

```text
x(x+d)-r(d+r) = (x-r)(x+r+d),
(m-r)(m-d-r)-(x+m)(x+m+d) = -(x-r+2m)(x+r+d).
```

Thus the sign of G is negative, and no summand division by x-r occurs.
Summing (C) gives the recurrence because G_x(0)=0 and
G_x(N+1)=0: `d+(N+1)=m+1` makes the second binomial factor zero.
This includes d=m (N=0), where the sum has one term.

At x=1 every term with 1<=r<=N vanishes. Indeed 1-r is the negative
integer -(r-1), where r-1<2m, hence one factor of P is zero. Consequently

```text
S(1)=choose(m,d)*(2m)!
    =choose(2m,m+d) * m! * (d+1)_m.
```

The second equality is factorial cancellation using d<=m. The claimed
right-hand side has the same recurrence by applying (B) with degree m
to each of its two Pochhammer factors. Since j(j+d)>0 for every positive
integer j, induction proves equality at all positive integers. Both sides
are polynomial evaluations, so their equality at infinitely many distinct
positive integers proves the real polynomial identity. There is no claim
that this recurrence determines values by division at its real zero factors.

To recover the one-based sum, put r=j-k. Its summation range is 0<=r<j.
If r>N the weight is zero. If j<=r<=N then P(j-r)=0 because
0<=r-j<2m. These facts justify changing the range to 0<=r<=N.
When d>m, every original summand and the right side are zero by the
out-of-range binomial convention. Real casts can then be replaced by
ordinary `Nat.ascFactorial` at the positive natural arguments.

## Attribution and primary-source check

This is an elementary proof of the finite binomial identity needed by the
already known inverse formula. The identity was not treated as an axiom or
inferred from the project's finite numerical tests.

The primary paper Böttcher, Fukshansky, Garcia and Maharaj,
[*Toeplitz determinants with perturbations in the corners*](https://www1.cmc.edu/pages/faculty/lenny/papers/toeplitz.pdf),
JFA 268 (2015), p.181, formula (22), was opened and checked. At delta=gamma=m,
its Gamma prefactor and diagonal factors cancel to the exact candidate
`diag((i)_m) B diag(1/(k)_(2m)) B^T diag((i)_m)` with
`B_ik=choose(k-i+m-1,m-1)` for k>=i. The same page attributes the formula
to Duduchava and Roch and gives the original-publication history. The
full 1974/1985 original proofs and the 2017 dedicated chapter were not read
here. No originality claim is made for the inverse formula.

The recurrence certificate and symbolic proof above are independently
derived here. They use no cited asymptotic theorem. Matrix inverse algebra,
uniform Riemann-sum estimates near the boundary and diagonal, and the
manuscript's actual kernel-limit input remain separate obligations.

## Pinned Mathlib APIs inspected

- `Nat.choose_succ_right_eq` in `Data/Nat/Choose/Basic.lean` supplies (A).
- `ascPochhammer_succ_left`, `ascPochhammer_succ_eval`,
  `ascPochhammer_eval_neg_coe_nat_of_lt`, `ascPochhammer_eval_one`, and
  `factorial_mul_ascPochhammer` in `RingTheory/Polynomial/Pochhammer.lean`
  supply the shift and base steps without Gamma functions.
- `Nat.cast_choose` in `Data/Nat/Choose/Cast.lean` supplies exact factorial
  conversion, with its lower-index bound discharged.
- `Finset.sum_range_sub` performs the finite telescoping.
- `Polynomial.eq_of_infinite_eval_eq` and `Set.infinite_range_of_injective`
  supply the real-polynomial extension.

Use only pinned available imports, standard kernel-checked proofs, and
symbolic finite sums. The source author runs no compiler. Local serialized
test evidence and any later GitHub Comparator evidence must be reported
separately, with exact source hashes.

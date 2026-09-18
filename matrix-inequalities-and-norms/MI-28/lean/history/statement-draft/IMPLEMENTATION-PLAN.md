# Implementation and reuse plan

The complete MI24 local332 source supplies real complex-matrix machinery that
was absent in the older MI28 preflight. Reuse its pinned successful source and
authorship, not an assumed theorem about an abstract norm. The current plan is
to vendor the necessary MI24 module closure unchanged, retaining namespace and
license/credit, and prove the transparent MI28 definition bridges. No full
closure is copied into this small checkpoint. MI24 publication and its later
review/runtime status must be checked again when selecting the actual reuse pin.

## Exact broader Furuta gap

MI24 `furuta_base` already proves, for X ≥ Y > 0, a ≥ 1 and 0 ≤ r ≤ 1,

    (X^(r/2) Y^a X^(r/2))^((1+r)/(a+r)) ≤ X^(1+r).

Its `furuta_grade_two` only extends the inner power a=2 to 0 ≤ r ≤ 2.
Its selected `furuta_half_power` has fixed outer exponent 1/2 and sandwich
exponent at most one. None of these is the general theorem MI28 needs:
canonical substitutions r=2/k and a=2/p are unbounded as k or p tend to zero.

There is a concrete internal extension route in Fujii (2010), Theorem 1.3,
printed p.30, already retained and read in the MI24 primary-source packet.
Assume the boundary statement at r1 for every a ≥ 1. Set

    X1 = X^(1+r1),
    Y1 = (X^(r1/2) Y^a X^(r1/2))^((1+r1)/(a+r1)),
    a1 = (a+r1)/(1+r1).

For 0 ≤ t ≤ 1, apply the existing base theorem to X1 ≥ Y1 and a1 ≥ 1.
Actual CFC power composition and same-base multiplication simplify the result
to the boundary statement at r1+(1+r1)t. This reaches [r1, 1+2r1].
Induction on an integer upper bound for r, with t=(r-N)/(1+N) in the new
interval [N,N+1], suffices. This is a finite symbolic induction theorem, not a
computation that enumerates a huge exponent-dependent matrix family. Then
Löwner–Heinz with exponent (a+r)/((1+r)q) ∈ [0,1] proves C06.
The actual extension and the necessary CFC algebra remain UNIMPLEMENTED.

## Canonical small-base route

1. Reuse positive CFC powers/inverses, polar conjugation, and order powers from
   SpectralPowers, PolarPowers and OrderPowers. Prove C02/C03 with factor order
   intact, using square-root positivity and uniqueness. Consume the certified
   half-exponent bounds when instantiating the CFC root identities.
2. C07 applies C06 with X=A^k, Y=|AB|^p, r=2/k, a=2/p, q=2. The exact
   admissibility condition is p ≥ k/(k+1). Its sandwich square is (ABA)^2.
3. C08 uses s=p(k+2)/(k+p), q=2/s; prove 1 ≤ p ≤ s ≤ 2 and the equality
   in the Furuta condition. The rest uses the existing all-real-exponent polar
   identity (WW*)^u = W(W*W)^(u-1)W*, inverse order and Löwner–Heinz.
   The source's negative-power Furuta comparison is derived here; do not add a
   second unproved negative-Furuta dependency.
4. C09 uses | |AB|^(-1) B | = A^(-1). Apply the proved swapped universal
   implication to this pair, then Löwner–Heinz with p/k and (k-p)/k. The latter
   exponent may be zero when k=p; no strict-positivity shortcut is allowed.
5. C10 partitions the exact real parameter region as in canonical Corollary 6.
   C11 rescales B by c^(-1/p), where c=||Z||>0 is the actual operator norm.

## The separately published large-base range is also a proof obligation

C12 may NOT be filled by a citation, an axiom, or a premise asserting the desired
norm comparison. The inspected author-uploaded primary paper is Ghabries,
Abbas, Mourad and Assi (2020), DOI 10.1016/j.laa.2020.07.013, Lemma 2.5,
printed pp.3–4 in the author manuscript. It reduces by compounds to a norm
comparison for 0 < s ≤ K and 0 ≤ t ≤ s:

    || X^((K-t)/2) Y^t X^((K-t)/2) ||
      ≤ || X^(K/2) (Y^(s/2) X^(-s) Y^(s/2))^(t/s) X^(K/2) ||.

Substitute X=A^(-1), Y=B, s=2, K=k, t=p. This reaches every k ≥ 2
and 0 < p ≤ 2. The primary proof's additional internal foundations are:

* Cordes/Araki operator-norm form: for PD X,Y and 0 ≤ u ≤ 1,
  ||X^u Y^u X^u|| ≤ ||(XYX)^u||.
* Its Lemma 2.3, of which this project only needs PD X,Y: for a,b ≥ 0,
  ||Y^((a-b)/2) X^2 Y^((a-b)/2)||
    ≤ ||Y^(-b/2) X Y^a X Y^(-b/2)||.
  These are positive congruent representatives of the source's product
  eigenvalues, so the operator norm has the correct spectral meaning.

Neither auxiliary inequality has been found as an available theorem in the
bounded pinned Mathlib/MI24 source search, and neither is proved by this packet.
The first can be developed by power-order contraction normalization. The second
requires a separate fully checked derivation (or an internal replacement route
for C12). Do not describe the full implementation as immediate until that gap
is closed. The full final statement is independent of how C12 is proved.

## Compounds, endpoints and determinant

Reuse MI24 CompoundAlgebra/CompoundSpectral/CompoundNorm: actual complex minors,
product/adjoint identities, unitary spectral decomposition, every real power,
PD preservation and norm = descending prefix product. The compound degree zero
has dimension one and empty eigenvalue product one; positive degrees j≤n have
positive dimension. No real-only exterior-space theorem may replace these.

Prove normalized compound covariance, then apply C11 or C12 to each pair of
compound matrices. Total products agree by the concrete determinant identity
det H=det Z=det(A)^(p-k) det(B)^p (positive real powers). All ingredients can
be reduced to diagonalization plus the existing det/product APIs.

At p=0, H=Z=A^(-k) directly. At k=0 and p>0, take k=1/(m+1), m→∞,
in the small-base norm inequality. C14 applies separately to each compound
pair; thus no theorem about continuity of sorted eigenvalues is needed. Fixed
positive A has a fixed spectral decomposition, and scalar λ^k is continuous in
k for λ>0. This is smaller than developing global matrix-power continuity.

For the determinant transfer, reuse root-authored MI24
`weighted_prefix_sum_nonpos`. For positive sequences a,b put
δ_i=log a_i−log b_i and w_i=a_i/(1+a_i). Prefix-product bounds give nonpositive
prefix sums of δ. Descending a makes w descending, with w≥0. C16 gives
log(1+a_i)−log(1+b_i) ≤ w_i δ_i, so Abel summation proves C17. This avoids
building a general majorization/Karamata theory. The concrete scalar tangent
can be proved by convexity/differentiation of log(1+exp), or an equivalent
scalar Young argument. Both alternatives remain proof work.

C18 factors the original determinants through det(A^k) and det(I+H/Z), using
similarity/det(I+UV)=det(I+VU) for the non-Hermitian right matrix. Matrix.PosDef
det_pos and the concrete product formula prove C19. C15/C17/C18 imply C20.

## Verification gates

Root alone elaborates the statement draft. Two independent statement referees
then derive/check the exact Comparator target and approve before freezing.
After implementation, source-bound local success for the entire closure,
kernel LeanCert consumption, exact elaborated types/universes, default standard
axioms and two nonauthor full-target reviews are required. Only then prepare a
standalone v0.4 manifest and one upstream PR, with final genuine Linux Comparator,
default-kernel replay, sandbox and negative controls. No such run is claimed here.

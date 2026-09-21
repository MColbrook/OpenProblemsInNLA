# Independent stable quadratic branch review

Verdict: **APPROVE** the mathematical branch construction, its statement fidelity, and the reviewed algebraic proof scope. The formula is literally the quadratic-formula choice used in unchanged manuscript Lemma 2, not a replacement argument that assumes an inside-root certificate. The module proves nonvanishing, its exact reciprocal quadratic equation, strict unit-disk inclusion for Re(a)>0, and the value at zero. It does not yet prove the full Lemma 2.

The coordinator reported `stable-root-algebra-02` exit 0 against the final source below. I read the log and its four axiom reports, all exactly `[propext, Classical.choice, Quot.sound]`. The earlier algebra01 attempt failed on casts, rewrites and tactic normalization; it is not accepted evidence. I reviewed the final corrected source and ran no compiler, Lake build, Comparator, or GitHub workflow. No source file was edited by this reviewer.

## Actual square-root branch

`stableQuadraticRoot` at line 13 is `(Complex.sqrt (1+a²)-a)²`, using Mathlib's principal square root. `complex_sqrt_sq` (lines 15–17) obtains its square identity from the actual complex-power theorem. No square-root property or branch premise is imported as a new axiom.

Write b=sqrt(1+a²). In `sqrt_one_add_sq_re_pos` (lines 19–38), the principal square root first supplies Re(b)≥0. If Re(b)=0 while Re(a)>0, the imaginary part of b²=1+a² forces Im(a)=0. Its real part then says a nonpositive number equals 1+Re(a)², a contradiction. This proves strict Re(b)>0 rather than assuming the desired branch.

The identity `(b-a)(b+a)=1` is proved directly from b²=1+a² (lines 40–43). Consequently b-a and its square cannot vanish, with no restriction on a (lines 45–51). Its inverse is b+a, so the inverse of the square is `(b+a)²`; adding the two squares proves `2-r-r⁻¹=-4a²` (lines 53–67). The sign and factor 4 are correct.

For Re(a)>0, the imaginary square identity gives Re(b) Im(a) Im(b)=Re(a) Im(a)². Because Re(b)>0, this implies Im(a) Im(b)≥0. Hence Re(b conjugate(a))>0. The norm-square difference is therefore strictly positive: |b-a|²<|b+a|². Combined with |b-a||b+a|=1, this gives |b-a|<1 and finally |r|<1 (lines 69–103). The proof correctly distinguishes conjugation from an unconstrained square-root choice. `stableQuadraticRoot_zero` (lines 105–106) gives r(0)=1, separately from the strict positive-real-part argument.

The hypothesis Re(a)>0 is substantive. For example a=i gives r=-1 of norm 1; extending the strict theorem to arbitrary Re(a)≥0 would be false. The module does not make that extension. Nonvanishing and the quadratic identity legitimately hold for all complex a.

## Exact identification with the unchanged manuscript

For 1≤ℓ≤m-1, the manuscript defines κℓ=exp(i(πℓ/m-π/2)). Its argument lies strictly between -π/2 and π/2, so Re(κℓ)>0, and κℓ²=-ωℓ. Put a=κℓ sin(θ/2). For 0<θ≤π, sin(θ/2)>0, so Re(a)>0. The proved equation becomes

`-4 a² = 4 ωℓ sin²(θ/2) = ωℓ (2-2 cos θ)`,

which is exactly manuscript (2). The strict norm inequality selects its inside root; the companion `(b+a)²` is its reciprocal and lies outside. The usual quadratic factorization therefore identifies the constructed expression with the unique inside root. That uniqueness identification and the κ/ω substitutions still need their own formal declarations; they are mathematical consequences, not results already in this module.

The first-order sign also matches (8): as a→0, b=1+O(a²), so r=1-2a+O(a²). Since a=κℓ θ/2+O(θ³), r=1-κℓ θ+O(θ²). Equivalently the derivatives are r_a'(0)=-2 and a_θ'(0)=κℓ/2, giving r_θ'(0)=-κℓ. This calculation is an independent mathematical check; the current file has no derivative or smoothness theorem, and I do not count it as a Lean result here.

## Remaining root and phase obligations

1. Define the actual κℓ and ωℓ with the original finite index set, prove their square/reality/positivity identities, and substitute the sine parameter into the current algebraic construction. Prove uniqueness as the root specified in (2), and distinctness of the stable roots for θ>0. Distinctness of the complete 2m root list is only needed on 0<θ<π; the unit roots coalesce at the endpoints.
2. Prove smoothness on a neighborhood of [0,π] and the derivative at zero. The relevant square-root argument avoids the nonpositive real axis: if Re(a)>0 and Im(1+a²)=0, then Im(a)=0 and 1+a² is positive. At θ=0 the argument is 1. This justifies using the ordinary principal square-root derivative API, with its actual slit-plane condition.
3. Derive the uniform exponential estimate |rℓ(θ)|≤exp(-cθ), c>0, from the first derivative at zero and compactness away from zero; take a finite minimum over ℓ. Strict norm inclusion alone is not the quantified estimate (6). Bounded logarithmic derivatives likewise still require the proved smoothness and nonvanishing on the compact interval.
4. Establish conjugation of the actual stable roots and the smooth endpoint extension of each phase factor. Principal square root does not commute with conjugation on its negative-real cut, so the cut-avoidance fact must be used rather than asserting unrestricted conjugation. The θ=0 factor `1-rℓ(θ)e^(-iθ)` vanishes; its argument at zero must be defined through the smooth cancelled extension with limiting value πℓ/(2m), not through the totalized raw `arg 0`.
5. Keep ψ as the **sum of the individual principal arguments** in manuscript (3). Replacing it with the principal argument of their product can change the branch and eigenvalue indexing: for m=6 the limiting sum is 5π/4 whereas the product's principal argument is -3π/4. Prove the phase endpoint sums and smoothness, and then η(0)=(m-1)π/2 and η(π)=π. These are not supplied by the current root algebra.

No manuscript edit is needed for this construction. These remaining items are genuine formalization work, not a discovered false step in Lemma 2. The independent review does not accept any later determinant estimate, phase indexing, expansion, inverse-kernel theorem, or MF-21 Target.

## Frozen source and evidence

| File | SHA256 |
|---|---|
| `MF21Restart/StableRootAlgebra.lean` | `f1b6459dc1372fba3bb5762c0cb557c4e082443e1be8d09506419bd43d59dde5` |
| `STABLE_ROOT_STATEMENTS.md` | `522987621255dcf06aae486d9904fafe37aca8a3721e37a8effa6aed024ea432` |
| `original-proof/solution.md` | `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa` |
| `reviews/REFEREE_STANDARDS.md` | `e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1` |
| `evidence/logs/stable-root-algebra-02.log` | `c6a56ef469581fe017484668a18b8403ded2764878291ca18c2560fd6a7e7d88` |

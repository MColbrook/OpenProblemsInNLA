# Independent review: actual tangents and normalized root differences

Verdict: **APPROVE** for the five printed results in `RootTangents.lean`
and the twelve in `RootDifferences.lean`, at the source hashes below.
I found no material correctness, source-fidelity, hypothesis, or trust
issue. The exact source, log, and current output hashes match the two
observed successful local JSON records. This review does not claim a new
compiler run or a GitHub Comparator result.

I independently read the actual sources, both statement locks, the
root/parameter definitions, and the relevant derivative, divided-slope,
and analytic-order library declarations. The statements implement the
distinct first-derivative and removable-difference argument following
manuscript (18), line 211. The pinned referee rubric has SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.
No reviewed source was edited and no compiler was run by this reviewer.
My previously authored `RootParameters` is an identified dependency,
not a new independent approval of that source.

## Actual tangent values and field of differentiation

`characteristicRootTangents` uses exactly the root list's four branches
and ordering: `-κ_1,...,-κ_(m-1), i, -i, κ_1,...,κ_(m-1)`.
`characteristicRoots_zero` proves that every actual root value is one.
`characteristicRoots_hasDerivAt_zero` differentiates each actual curve
with respect to the real parameter. The exponential derivative is i;
inverting it gives -i. For the stable curve, r'(0)=-κ and r(0)=1, so
the inverse derivative `-r'(0)/r(0)^2` is +κ. The signs and inverse
orientation are correct, with no tangent value supplied as a new premise.

The first failed local log shows two construction paths for the real
module structure on ℂ: the normed-algebra path and the real inner-product
space path. In the successful current source, `convert!` aligns these
structures and the displayed function forms while the ordinary derivative
calculus proves the mathematical assertion. It does not change the scalar
field to ℂ, postulate equality of unrelated scalar actions, or add a proof
axiom. The current local reports contain no `sorryAx`; the failed first
attempt is not used as verification evidence.

The endpoint and derivative results do not require m≥2. At m=0 the list
is empty; at m=1 it consists of z and z⁻¹, with the two expected derivatives.
The distinctness theorem deliberately uses m≥2, which covers the full
manuscript domain without changing its target.

## Distinctness comes from the actual parameters

`rootKappa_injective` squares equal κ values, applies κ²=-ω, and uses the
proved injectivity of the actual root-of-unity parameter on `Fin m`.
It does not use the false general assertion that squaring is injective.
`characteristicRootTangents_re_regions` separates the stable tangents by
strictly negative real part and exterior tangents by strictly positive
real part. The remaining two have real part zero and imaginary parts 1
and -1. Within each noncentral group, the proved κ injectivity and justified
natural-index arithmetic recover equality of indices.

Consequently `characteristicRootTangents_injective` establishes concrete
pairwise distinctness rather than taking a distinct tangent list as input.
`characteristicRoots_sub_hasDerivAt_zero` and
`characteristicRootTangents_sub_ne_zero` have the same a-minus-b orientation.
Together with the common root value one, they supply the manuscript's
simple-zero assertion for every pair of different root positions.

## Divided differences use the Vandermonde orientation

`normalizedCharacteristicDifference m i j` is the actual Mathlib
`dslope` of `root_j-root_i` at zero. Its value at zero is therefore the
actual derivative `tangent_j-tangent_i`, which the corresponding theorem
proves. Off zero, the source proves the literal formula
`theta⁻¹*(root_j-root_i)` with theta cast into ℂ. The real scalar action
is explicitly converted using `Complex.real_smul` and `Complex.ofReal_inv`.
It never replaces the derivative-completed endpoint with totalized division
by zero.

`characteristicRoots_sub_eq_mul_normalizedDifference` proves the exact
identity `root_j-root_i=theta*normalizedDifference` for every real theta,
including zero. The subtracted endpoint value is zero because both roots
are one there. This orientation agrees with `Matrix.det_vandermonde`,
whose factors are later-index root minus earlier-index root.

The analyticity proof uses the actual globally regular root curves and
the already proved analytic-dslope lemma. I checked the pinned library's
`Analysis/Calculus/ContDiff/Defs.lean`: its order type is `ℕ∞ω`, and
`⊤` denotes the analytic order ω, while the distinct lower element ∞
denotes infinite differentiability. Thus using
`ContDiff ℝ ⊤ ...` followed by `.contDiffAt.analyticAt` is legitimate.
This is not an inference from arbitrary smoothness to analyticity. The
claimed analyticity is in the real parameter, as the lock states; no
global holomorphic extension in a complex parameter is asserted.

Nonvanishing at zero uses the actual distinct tangents, with the argument
order reversed when necessary to obtain j-minus-i. Positive-parameter
nonvanishing uses the exact factorization and actual root injectivity on
`0<theta<π`. The strict upper endpoint is essential: for the two central
indices the difference vanishes at π. No global nonvanishing claim is
mistakenly inferred from global analyticity, and i=j is correctly excluded
from nonvanishing statements.

## Finite products and exact powers

`normalizedCharacteristicDifferenceProduct` is the literal finite product
over the supplied ordered pairs. Its analyticity and regularity use finite
products of the proved actual factors. Its zero value is the exact product
of tangent differences. The nonvanishing premise requires only that each
pair has different components. It allows arbitrary pair collections,
including the empty product one and both orientations of a pair; the
product retains the corresponding signs.

`characteristicRoots_differenceProduct_eq_pow_mul` factors one theta
from each actual difference and proves the power is exactly `pairs.card`.
There is no assumption that a desired Vandermonde quotient exists, and
no determinant exponent is guessed. Identifying the actual pair sets and
their total exponent, and using them to construct the coefficient a_S,
remain separate obligations, as the lock explicitly says.

No bound on the normalized coefficient or its derivative is proved here.
Nonvanishing of the relevant denominator sublists through π also requires
the separate collision/separation argument. These seventeen approved
ingredients are not a completed MF-21 target and do not increase the
original-problem count.

## Local evidence and exact hashes

I read RootTangents02 and RootDifferences01 JSON records and recomputed
their current source, log, and `.olean` hashes. Every compared hash matches.
Both records give exit 0, source unchanged, and exact local commands
`lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/MODULE.olean
MF21Restart/MODULE.lean` for the corresponding module. The observed logs
print five and twelve results, all depending only on
`[propext, Classical.choice, Quot.sound]`. The RootTangents linter warnings
are optional proof-style cleanup, not a mathematical finding.

The commands were run by the coordinator, not this reviewer. No independent
compiler execution, GitHub workflow, Comparator/kernel-sandbox run, or final
target verification is claimed. No custom axiom, placeholder, unsafe shortcut,
`native_decide`, or numerical oracle appears in the reviewed sources.

| File | SHA256 |
|---|---|
| `MF21Restart/RootTangents.lean` | `a37f2ec6cc1c1385b4219cb927e2164e0cfab3f584cd912ac48974391f7a299f` |
| `ROOT_TANGENTS_STATEMENTS.md` | `10de53b07d9468249979bacea0f848c59c65f21b84acfeff4a5dc533a30dded7` |
| `MF21Restart/RootDifferences.lean` | `1ee5fd0829c87ae76fddadd582ab5a4dc14392d0b3625bd89051223e025db856` |
| `ROOT_DIFFERENCE_STATEMENTS.md` | `68438dd243ebc3c3556929eff1e4f1233c1272d930e3ef85530f0040d03222b5` |
| `evidence/logs/root-tangents-02.json` | `a96fff791efef7410acef207fc8b39a796820956037eba5ae804ef764726953c` |
| `evidence/logs/root-tangents-02.log` | `8c4b223692a533d72521572273844061fa080741ca93c0167f8c5a49d63f4062` |
| `.lake/build/lib/lean/MF21Restart/RootTangents.olean` | `6eeeadb7501f9d995dfd780997ff10598e369775da24936db070e2eac23eff7e` |
| `evidence/logs/root-differences-01.json` | `b9be0a2a07088731441193080120361debfa67279fff576f4cf7e18656e77450` |
| `evidence/logs/root-differences-01.log` | `451bb4e76dae87858172089e522d5ff1a8d91b0ee8ee4c5d350b0258098baa65` |
| `.lake/build/lib/lean/MF21Restart/RootDifferences.olean` | `afa27f461df2c845058cff14800b3ac276eb43bdb006cc99f4413c64d043e280` |

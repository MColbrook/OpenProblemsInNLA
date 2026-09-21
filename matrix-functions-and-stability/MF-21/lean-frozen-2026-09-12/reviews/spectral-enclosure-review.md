# Independent review: actual Fourier Toeplitz spectral enclosure

Verdict: **APPROVE** the three stated intermediate results. No material
source-fidelity, statement, or proof defect found. These establish strict
spectral enclosure; they do not prove the later window counting or MF-21.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. The reviewer
did not author or edit `SpectralEnclosure.lean` and ran no compiler. The
pinned referee standards have SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Sources and actual local evidence

The following hashes were independently recomputed from current files.

| Artifact | SHA256 |
|---|---|
| `MF21Restart/SpectralEnclosure.lean` | `897e91a69bf25da532691880d9d6832dc0167e43fae5b8d7271b74359762c4f0` |
| `SPECTRAL_ENCLOSURE_STATEMENTS.md` | `05046c748d4994713092b558bf7004a2abced2b02b7a36767c5c5c818c6b8ee6` |
| `evidence/logs/spectral-enclosure-03.json` | `8dfdb467cdb56eb81661d33591c80a7ce232a9c444cfe31fcdc6bd542e0c03de` |
| `evidence/logs/spectral-enclosure-03.log` | `0fbef97c1de5049c162404dc87ddeb55e2b92f384979d3345e639ac5d5077d6f` |
| `.lake/build/lib/lean/MF21Restart/SpectralEnclosure.olean` | `612f29fa51463bb45a64c7f2c51a44492133146c17be267295582c0af24ba4b4` |

The JSON matches the source, log and output hashes above and records
exit_code=0, source_unchanged=true, `LEAN_NUM_THREADS=1`, and
`lake env lean -j1 -M4096 -o
.lake/build/lib/lean/MF21Restart/SpectralEnclosure.olean
MF21Restart/SpectralEnclosure.lean`. All three printed declarations use
only `propext`, `Classical.choice`, and `Quot.sound`; there are no error
lines or `sorryAx`. The unused-hypothesis warning at line 190 is explained
below and does not undermine the proof.

The unchanged manuscript `original-proof/solution.md`, SHA256
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`,
line 219 gives precisely this quadratic-form argument before Lemma 4.
Definitions of the actual integral coefficient, Toeplitz matrix and
one-based eigenvalues are at `Definitions.lean:18–53`, SHA256
`35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51`.

## Mathematical audit

1. **Exact Fourier quadratic form.** Lines 26–53 define the nonnegative
   real function `(sum v_i*cos(i*theta))^2+(sum v_i*sin(i*theta))^2` and
   expand it into `sum_i sum_j v_i*v_j*cos((i-j)*theta)` using the cosine
   subtraction identity. This is exactly the squared complex modulus of
   the finite trigonometric polynomial. Lines 55–107 identify its weighted
   integral with `star v dot (toeplitz m n * v)`, retaining the normalization
   `1/(2*pi)`, interval `[-pi,pi]`, and integer difference i-j from the
   original coefficient. The finite sums are exchanged with integrals only
   after explicit continuity/integrability proofs.

2. **Strict unweighted positivity is proved.** Lines 109–126 use the
   already proved actual order-zero Fourier coefficient to establish
   `toeplitz 0 n=1`. The corresponding integral is therefore exactly
   `2*pi*(star v dot v)`, positive for every v!=0. There is no assumed
   nonzero-polynomial or almost-everywhere nonvanishing premise.
   The reused `FourierStencil.lean` has SHA256
   `c7c94724b95fffb35abf8f682a921a0badcca1de19e41b99b0502cd9349cf809`.

3. **The weighted positivity argument is sound at exceptional points.**
   Lines 132–165 prove the needed general helper from continuity,
   nonnegativity of p, positive unweighted integral, and strict positivity
   of w on `(-pi,pi)` away from zero. Lebesgue measure of the excluded
   singletons is zero. The interval integral is represented using
   `Ioc(-pi,pi)`, so -pi is already excluded; pi and zero are explicitly
   removed almost everywhere. If the weighted integral were zero, its
   nonnegative integrand would vanish almost everywhere; w>0 then forces
   p=0 almost everywhere and contradicts its positive unweighted integral.
   Continuity supplies each required interval-integrability premise.

4. **Both actual weights satisfy the strict inequalities.** Lines 167–178
   prove `symbol m theta>0` in the punctured open interval by nonvanishing
   of sin(theta/2) and the even exponent 2m. This remains true for m=0,
   where the symbol is one. Lines 180–188 use cos(theta/2)>0 to prove
   `(2*sin(theta/2))^2<4`, then raise to the strictly positive order m.
   Consequently the second weight `4^m-symbol m theta` is positive on the
   open interval for m>=1; no false strict assertion is made at +/-pi.

5. **Positive definiteness concerns the exact matrix and shift.** Lines
   190–198 use the actual Hermitian Toeplitz matrix and its quadratic form
   to prove `toeplitz_posDef`. Its hypothesis m>=1 is unused because this
   lower result also holds at m=0; keeping the common hypothesis of the
   locked pair of results is harmless, and no important case is lost.
   Lines 200–239 prove the upper quadratic integral for
   `4^m * identity - toeplitz m n`, including the correct scalar and sign,
   and establish its positive definiteness. The upper result genuinely
   requires m>=1: at m=0 that complement is zero.

6. **The accessor is not replaced by an arbitrary spectral value.** Lines
   242–263 assume exactly `1<=j<=n`, use the proved equivalence with a real
   characteristic root, and obtain a nonzero real eigenvector. Applying
   the two positive quadratic forms to it yields lambda>0 and
   `4^m-lambda>0`, since its squared norm is positive. The imported
   `EigenvalueBridge.lean:31–37`, SHA256
   `e07040bc9e98995f4c6ead6d7d9bbd3754c68acc36c71b115e4e117453c4c811`,
   is tied to the unchanged sorted one-based accessor. No out-of-range
   totalized zero is included. For n=0 the two matrix statements are
   appropriately vacuous, while the eigenvalue hypotheses are impossible;
   for every positive n the result covers all n actual indexed values.

## Review and trust scope

The four-module project import closure is exactly Definitions,
FourierStencil, EigenvalueBridge and SpectralEnclosure. A read-only scan
found no `sorry`, `admit`, custom axiom, unsafe declaration, `native_decide`,
or `Challenge` import. The new proof uses no numerical certification or
finite sampling and moves no enclosure assertion into a hypothesis.

This is an independent review of the new enclosure module and its use of
the imported interfaces. Because this reviewer authored FourierStencil,
its proof internals are excluded from the independent-authorship scope
here; its actual integral theorem is reused rather than redefined.
The three conclusions agree with the statement lock. They establish the
spectral prerequisite only: no proof of the inverse symbol map, ordered
window identification, asymptotic expansion, or full Target is claimed.
No GitHub Comparator/kernel/sandbox run was performed. Counts of original
mathematical targets or complete Lean verifications do not increase.

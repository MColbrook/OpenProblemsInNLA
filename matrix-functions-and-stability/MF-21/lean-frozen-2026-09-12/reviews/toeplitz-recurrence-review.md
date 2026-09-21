# Independent Toeplitz convolution review

Verdict: **APPROVE**, for the exact operator identity
zeroGhost_convolution_eq_toeplitz_mulVec.

Reviewer: /root/mf21_restart_lean_audit, 20 September 2026. I did not write
or edit ToeplitzRecurrence.lean or FiniteRecurrence.lean, and I launched
no compiler. I authored FourierStencil, so its correctness is treated
as a previously checked dependency here, not independently re-reviewed
by its author. This report checks the new operator proof and its exact
uses of that dependency. The pinned referee standards are at
/Users/georgestepaniants/Research/project/lean-verification/REFEREE_STANDARDS.md,
SHA-256 e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1.

## Exact source scope

Paths are relative to the MF21-restart directory.

| Path | SHA-256 |
| --- | --- |
| MF21Restart/ToeplitzRecurrence.lean | 491d34f1776dcc4428b4b90071cdba5f1b8054538ee81876a6b046cafae04b22 |
| TOEPLITZ_RECURRENCE_STATEMENTS.md | c06f9f9c8acdde1c65956b7ccbf16c8e30c6bb96e3c8ee5c8dfc2f718ab55143 |
| MF21Restart/FiniteRecurrence.lean | a252b76405c506b2b850e288c41769083267a23a4e454c424096a6002e4db39a |
| MF21Restart/Definitions.lean | 35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51 |
| MF21Restart/FourierStencil.lean | c7c94724b95fffb35abf8f682a921a0badcca1de19e41b99b0502cd9349cf809 |
| original-proof/solution.md | 6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa |
| evidence/logs/toeplitz-recurrence-01.log | d785f7cc3fc2418f0026a5d52617e06c2f80d6623c303081b9c215583b6ac9c4 |

FiniteRecurrence.lean:35–40, the zeroGhostExtension definition and its
middle-value lemma, are included in this dependency review. This report
does not independently certify all the other extension/solution theorems
in that module.

## Fidelity and proof checks

1. ToeplitzRecurrence.lean:14–19 uses the unchanged real integral-defined
   toeplitz from Definitions, mapped entrywise through Complex.ofReal.
   The action is on an arbitrary complex vector and every actual row
   k : Fin n. No eigenvalue equation, recurrence equation, or artificial
   bandedness hypothesis is present. It exactly matches the locked
   TOEPLITZ_RECURRENCE_STATEMENTS.md.

2. FiniteRecurrence.lean:35–36 places the vector component v(i) at natural
   index m+i and returns zero outside [m,m+n). Its subtraction t-m is
   guarded by interval membership. This is precisely the manuscript's
   shift of original ghost indices 1-m,...,0 and n+1,...,n+m by m-1
   (solution.md:149–159): the zero-based interior vector index i maps
   to m+i, the left ghost block to 0,...,m-1, and the right ghost block
   to n+m,...,n+2m-1.

3. In ToeplitzRecurrence.lean:31–36 the condition k+t=m+j gives
   t-m=j-k=-(k-j), with all differences explicitly taken in the integers.
   Applying fourierCoeff_neg is therefore required and is correctly
   done. This avoids replacing the actual Toeplitz convention a(k-j)
   by a reversed-frequency convention without justification.

4. Lines 27–30 show that every nonzero convolution term has an interior
   zeroGhostExtension index. The forward reindexing at lines 37–48 uses
   j=k+t-m and proves injectivity using these bounds, so natural
   subtraction cannot collapse distinct active terms.

5. For the converse reindexing at lines 49–64, a nonzero matrix summand
   implies its Fourier coefficient is nonzero. The proved concrete
   Fourier support theorem then yields |k-j|<=m. Those integer bounds
   justify t=m+j-k in Fin(2m+1) and the exact identity k+t=m+j.
   The previously proved term equality supplies nonvanishing and the
   correct inverse correspondence. No assumption that all matrix
   entries or vector components are nonzero is introduced.

6. The use of Finset.sum_bij_ne_zero discards exactly the zero terms on
   either side. It is a finite symbolic reindexing, not a convergence
   argument or finite-size enumeration. The endpoint t=2m is included,
   and both extreme Fourier frequencies -m and m occur. The cases
   m=0 and n=1 are meaningful and correctly handled. At n=0 there is
   no row k; the pointwise operator assertion is appropriately empty.

The integer-frequency convention, complexification, center k+m, and
inclusive bandwidth all match the intended finite Fourier equation.
The result is a concrete operator identity rather than an abstract-array
wrapper. It does not itself construct eigenvectors, establish the
boundary determinant criterion, or identify the one-based ordered
eigenvalues; those require the separate recurrence and spectral bridges.

## Trust and execution scope

The reviewed source has no sorry, admit, custom axiom, unsafe shortcut,
or legacy import. I inspected the hashed local log: its sole public
axiom report contains exactly propext, Classical.choice, and Quot.sound,
with no error or sorryAx. The coordinator reports the corresponding
toeplitz-recurrence-01 process exited 0. I did not launch that process.

This approval is for the stated source bytes and operator theorem.
It does not certify an unrun Comparator contract or the complete MF-21
Target, and it does not increase a completed-problem count.

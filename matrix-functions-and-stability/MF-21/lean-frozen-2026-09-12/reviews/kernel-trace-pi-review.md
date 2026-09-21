# Independent kernel, trace-arithmetic, and pi-port review

Verdict: **APPROVE**, for the exact scalar integral identities, arithmetic
irrationality inference, and unconditional pi-transcendence bridge reviewed
below. This does not approve an inverse-kernel limit, a trace-series
identification, the complete MF-21 Target, or an unrun Comparator result.

Reviewer: /root/mf21_restart_lean_audit, 20 September 2026. I wrote none of
the reviewed source files, made no edits to them, and launched no compiler.
My own Fourier and bulk-decay modules are excluded from this independent
review. I coordinated with the KernelDiagonal author, who froze the source
at the hash below after its first compiler-feedback correction.

The governing review standard is
/Users/georgestepaniants/Research/project/lean-verification/REFEREE_STANDARDS.md,
SHA-256 e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1.

## Exact source identity

Paths are relative to the MF21-restart directory. All hashes were computed
directly from the reviewed files, rather than copied from another review.

| Path | SHA-256 |
| --- | --- |
| MF21Restart/KernelDiagonal.lean | 4dfd060f6243be832ed05ec61de94160cd9086fbb5dd99df7b6f22f1a4f6bbd2 |
| KERNEL_DIAGONAL_STATEMENTS.md | 471e45fd48666252fa5b69ec29b017f4b9d3ff5d964761a41f5a818f7bf23b9c |
| MF21Restart/TraceIrrationality.lean | 886aa32e8f60a28e4ec339d616d17e67e6f1241b99ba51020ad1e48815cd73d9 |
| TRACE_IRRATIONALITY_STATEMENTS.md | 65e3598062876fb96e03b7098adb25a820800900e3861579ecea4ef8d084f14b |
| MF21Restart/PiTranscendence.lean | 63978695081b2c4e863609090b0ae358470ae7e64e17893385237339d8315cc9 |
| LeanFormalizations/NumberTheory/Transcendence/ETranscendental.lean | 7cf361e9979a0b68e932a6105c89a0e74bed28d4d3070ac947b370c681942ef0 |
| LeanFormalizations/NumberTheory/Transcendence/PiLindemann.lean | d7a7e51ecfa31365cf163558536e3702bc6b60d6984fa8bf6560dfc8fb07e030 |
| LeanFormalizations/NumberTheory/Transcendence/HermiteLindemann.lean | bd754566761fe4e7b34441420962d2d5d1d1c5a409ebca41e9346f55258df108 |
| LeanFormalizations/NumberTheory/Transcendence/MonicRootSums.lean | cad726aa56114f33a80a75bafba9fbe87d7a30e9da2dfff1d43efc482f40555c |
| LeanFormalizations/NumberTheory/Transcendence/SubsetSumEsymm.lean | b9196dc2dc307cd7c9d32f703dab028c7bfecf2c036745c105b81581ba01503f |
| LeanFormalizations/NumberTheory/Transcendence/PiTranscendental.lean | 7ffa9e9a3734edce153443ced0a144515ab539091634dc9ab497066873aefdb6 |
| original-proof/solution.md | 6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa |
| vendor/gotrevor-pi/fetch-manifest.json | 79b255231ebf14ab66a949e936ecc14b22241b7371b6f18f7eb8d5e24322076f |
| vendor/gotrevor-pi/local-files.json | 5bdf5d3a54e245dfbb2469d4757fdf07d8085d2a10d160032d2e9d095022ff59 |
| vendor/gotrevor-pi/LICENSE | b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1 |

## KernelDiagonal source fidelity and proof

KernelDiagonal.lean:23–26 states the exact scalar substitution integral
for every natural k and 0<x<=1. These are inhabited hypotheses. At k=0
the formula reduces to the integral of 1/t^2, and at x=1 both sides are
zero. The excluded singular lower endpoint x=0 is not silently totalized
into an assertion about a Green kernel.

Lines 28–32 prove every point of the integration interval is nonzero.
Lines 33–45 calculate the derivative of 1-x/t as x/t^2 and prove the
required continuity. The scoped elaborator transparency option at
lines 38–40 resolves a real-module instance transport; it changes no
mathematical hypothesis and introduces no trusted axiom or unsafe code.

Lines 46–67 apply Mathlib's actual integral_comp_mul_deriv theorem, prove
the transformed integrands equal, compute the endpoints 0 and 1-x, and
evaluate the resulting polynomial integral. All divisions by x or t are
backed by their nonzero proofs. The change of variables is a conclusion
of this argument, not a supplied premise.

The second statement at lines 71–77 retains exactly the two x^m factors,
two (t-x)^(m-1) factors, t^(2m), and factorial denominator in manuscript
solution.md:322–325, equation (27), after setting y=x. Lines 78–98 combine
the powers, specialize k=2m-2, and cancel the positive x with the correct
integer arithmetic under m>=1. The resulting polynomial is exactly
solution.md:330–332, equation (28). For m=1 it gives x(1-x), as expected.

Both theorem types match KERNEL_DIAGONAL_STATEMENTS.md. The scalar
calculation is valid for all positive x<=1, but the cited kernel formula
(27) is used directly on the diagonal only when x>=1/2. The module and
lock correctly leave identification with that kernel, reflection to the
other half-interval, endpoint continuity, and inverse-kernel convergence
as separate obligations. They do not claim equation (28) for a defined
Green operator merely by evaluating this integral.

## TraceIrrationality exact arithmetic scope

TraceIrrationality.lean:12–15 proves precisely that
u-v/pi^k is irrational for rational u, nonzero rational v, and positive
natural k. The proof uses the unconditional pi-transcendence bridge,
Mathlib's Transcendental.pow, Transcendental.irrational, and the proved
closure of irrationality under division of a nonzero rational by an
irrational number and subtraction from a rational.

This correctly uses transcendence, since irrationality of pi alone would
not justify irrationality of every positive power. The exclusions k=0
and v=0 are essential: either can make the displayed expression rational.
Lines 17–20 specialize k=2m and positive v under m>=1, a valid extension
containing the manuscript's m>=3 cases. No spectral or trace limit is a
hypothesis.

The statements exactly match TRACE_IRRATIONALITY_STATEMENTS.md and the
arithmetic inference in manuscript solution.md:366–380. This module does
not prove that the actual series in (31) has this form. The odd/even zeta
identities, rationality of Euler's normalized even zeta value, positivity
of the actual finite tail, the dominated-convergence limit, and its
comparison with the rational trace integral remain separate. In
particular, no conflicting pair of limits is assumed to obtain a vacuous
negation of Target.

## External pi proof and port

PiTranscendence.lean:12–13 has the unconditional type
Transcendental Rational Real.pi, using the ordinary Mathlib predicate,
rational field, and real pi. It applies the capstone at
PiTranscendental.lean:24–26, which supplies the sole remaining
subset-symmetric-sum premise of MonicRootSums with the proved theorem in
SubsetSumEsymm. There are no section variables or extra typeclass
hypotheses at either final declaration.

I inspected all six local source files and the following closure:

- PiLindemann:71–128 derives the exponential subset-sum relation and
  proves the positive integer zero-subset count using the empty subset.
  Lines 155–250 establish its analytic impossibility by applying
  Mathlib's proved exp_polynomial_approx, constructing an integer of
  norm less than 1, and proving that integer nonzero modulo a prime.
  The scaled root-sum integrality premise is made explicit there.
- PiLindemann:255–350 reduces that integrality premise to monic
  polynomial root sums. MonicRootSums:37–111 supplies those sums through
  Vieta, Newton identities, and polynomial evaluation; lines 125–174
  apply it and construct the needed integer polynomial by removing
  zero roots and clearing denominators.
- SubsetSumEsymm:33–151 proves rationality of the symmetric functions
  of all subset sums, by invariance under permutation, the fundamental
  theorem of symmetric polynomials, and Vieta. MonicRootSums:186–223
  then applies this construction to the conjugates of i*pi under the
  temporary contradiction assumption that pi is algebraic; the ordinary
  Euler identity supplies exp(i*pi)=-1.
- HermiteLindemann:26–29 only transports algebraicity from the real to
  complex field. Its historical discussion of a removed axiom is a
  comment; no such axiom declaration remains in the source. ETranscendental
  supplies the factorial-decay and prime-selection infrastructure used
  by the analytic impossibility argument.

Thus the intermediate conditional lemmas are actually supplied with
proofs at the final theorem; their hard premises are not transferred to
MF-21 as assumptions. Static scans after removing nested and line comments
found no sorry, admit, custom axiom, unsafe, native_decide, run_tac,
initialize, implemented_by, or custom declaration shadowing the target
definitions in any of these nine reviewed Lean files. This source review
does not re-audit all foundational Mathlib proofs; the reported final
axiom dependency check covers the proof actually used by the bridge.

For provenance, I independently compared the six files against the
retained raw downloads in /private/tmp/mf21-pi-dependency/gotrevor at
immutable commit 3a24a73416f83c32b4d4a2ac09588524c6291650 and verified every
download hash against fetch-manifest.json. This comparison used the
retained downloads, not a fresh network fetch. ETranscendental,
PiLindemann, HermiteLindemann, and PiTranscendental are byte-identical.
MonicRootSums changes only its broad Mathlib import to the targeted Newton
identities and tactic imports, with a local-port comment. SubsetSumEsymm
narrows its Mathlib imports and adds Multiset.powersetCard_zero_right to
the empty-multiset simplification at line 38. No theorem statement,
hypothesis, arithmetic normalization, or trust boundary was weakened.
local-files.json accurately records those two modifications. The
immutable source URLs, original authorship, and Apache-2.0 license are
retained; this is an external contribution, not a new MF-21 theorem of
pi-transcendence.

## Local evidence and remaining verification boundary

I read the logs below and independently computed these hashes.

| Log | SHA-256 |
| --- | --- |
| evidence/logs/kernel-diagonal-02.log | 28ffc78a12e6fbc633b377511537ddc0855f95fe88e8844647ca8842e7eb18d1 |
| evidence/logs/trace-irrationality-02.log | 96be4379fcffb5568f53cd0b6e3d615f5b63b4a62776f89595abd61271d2002e |
| evidence/logs/pi-transcendence-01.log | c00ffff999ca9d88dfc878252adff412287d06571644639a9d5899a87b38c91e |
| evidence/logs/vendor-monic-02.log | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| evidence/logs/vendor-subsetsum-03.log | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| evidence/logs/vendor-pi-01.log | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |

The first three logs contain respectively two, two, and one final axiom
reports, all limited to propext, Classical.choice, and Quot.sound. They
contain no errors or sorryAx. KernelDiagonal has harmless unused-tactic
warnings. The last three logs are empty; an empty log is not by itself
evidence of a process exit status.

The older vendor record
evidence/vendor-runs/20260920T190739652073Z/record.json, SHA-256
892c79c8b85089fc9c5f32cc32966665f3c52efba06819fdfaa5a0a17977409c,
records successful first-three-module runs and an exit-134 failure of
the original broad-import MonicRootSums. Its passed=false status is
correct and cannot be cited as a successful current closure run. The
subsequent port has different hashes as listed above. The coordinator's
source-matched final record must separately retain the successful runs
for those current bytes and the two new MF-21 modules.

After the log inspection, the coordinator explicitly confirmed that
kernel-diagonal-02 and trace-irrationality-02 both exited 0 at the source
hashes in this report. Each produced the two standard-only axiom reports
described above. This confirms those individual local process outcomes;
it does not change the separate whole-project and Comparator scope.

This review finds no material statement, proof, or port defect in the
specified sources. It does not assert a fresh whole-project run, a
GitHub Comparator/kernel/sandbox pass, or completion of MF-21. New exact
contracts and their final execution evidence remain an integration step.

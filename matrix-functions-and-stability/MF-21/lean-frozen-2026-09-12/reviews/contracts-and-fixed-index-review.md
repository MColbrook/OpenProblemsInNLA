# Independent fixed-index, numerical, and contract review

**Verdict: APPROVE within the stated partial scope.** No material statement,
proof, numerical-certification, or contract-design defect was found in the
reviewed sources. This is not approval of the full MF-21 target, a Comparator
pass, or completion of any original problem.

Date: 20 September 2026. Review follows the pinned REFEREE_STANDARDS.md
(SHA-256 e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1).
This reviewer did not write FixedIndex.lean or Numerics.lean and reviewed
their statements and proofs independently. No compiler or Comparator was
run by this reviewer. No proof or contract source was edited.

**Independence exclusion:** this reviewer wrote BulkDecay.lean and does not
issue an independent proof or mathematical-adequacy verdict for it here.
The bulk declaration's Challenge/Solution textual agreement and import
boundary were checked as part of contract administration only.

## Exact reviewed sources

| Source | SHA-256 |
| --- | --- |
| MF21Restart/Definitions.lean | 35a74047a81a9b7526e9bf039880ca8f07ae33314e2b5b960ab254e02fca4b51 |
| MF21Restart/FixedIndex.lean | da98fb1baae1b4b1736f5be8f03261b4a609182342df6158ac2394713313fc28 |
| MF21Restart/Numerics.lean | 9d8eb86229773759393cecd14b2651dfc6a994c270dc1ee82d3131c1af60bc42 |
| MF21Restart/StatementBridges.lean | 90992b2cf34bbbefdf9da9c04b814a693faba7ec8d48b16bdf8d00948c4db057 |
| MF21Restart.lean | 11baffe50a6f760f5f6296f5e6ff4726310597e7a3b0d1475c83167968f10b35 |
| Challenge.lean | acb7ab31e0b3ab43c149ec404a03078d03f2936f25af71fa5f0c102e9084c963 |
| Solution.lean | ae69cdafd3ce590a00fa106716cdbc8683158069e7d782a10dfc1118d0d67dcb |
| comparator.json | 51bf180b3ba7c433a33c94e01343066bfcc982579ef6e472d826b6e956c37cd7 |
| Audit.lean | 99040f11643ac13985d3319dddd8b689d35a02593a7cbb528b216b2e0a1b7eba |
| STATEMENTS.md | 6709fd19a3765c83ce16986780963e1f22ae49472b5ea7f013e968f37ab27691 |
| original-proof/solution.md | 6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa |

Line references below refer to these exact versions. Definitions.lean has
not changed since the earlier independent statement approval.

## Fixed-index mathematics and proof

FixedIndex.lean lines 28–40 derive the phase quotient limit by dividing the
actual eventual implicit equation by the eventually positive h_n and using
continuity of eta at zero. The limit is derived; it is not among the
hypotheses. The lemma does not need h_n->0 separately because y_n->0,
the equation, and nonzero denominators already suffice for this quotient.

Lines 19–24 and 44–59 use the exact identity

    2*sin(y/2) = y*sinc(y/2).

Continuity of sinc supplies the factor tending to one. This proves the
correct 2m-power scaling for the concrete sine-power symbol. The proof
handles y_n=0 and does not impose an unnecessary nonzero-angle
hypothesis. The algebraic factorization also remains valid at h_n=0 in
this intermediate lemma because Lean's field division is totalized; the
main application separately has strictly positive h_n.

Lines 63–93 divide the assumed error of size C*h_n^(2m+1) by the positive
h_n^(2m), bound the resulting norm by C*h_n, and use h_n->0. The power
and sign are correct. An explicit assumption C>=0 is unnecessary:
the eventual absolute-value inequality and positivity of h_n already
force the required nonnegative upper bound. The generic assumptions are
consistent, for example with eta=0, y_n=b*h_n, ev_n=symbol m y_n, and C=0.

The concrete application at lines 100–136 has the correct logical shape:

- j is fixed and satisfies 1<=j.
- hU is the **hypothetical uniform critical-order bound**, intended for a
  later contradiction.
- The critical Taylor estimate uses the same entire expansion sum as hU,
  including its k=2m coefficient.
- The phase equation, y_n->0, and continuity of eta are explicit earlier
  obligations.
- The conclusion concerns the actual one-based eigenvalue m,n,j and its
  correct multiplication by (n+2)^(2m).

The uniform-bound hypothesis is genuinely used: it is unpacked at line 114
and applied at line 131 after ensuring n>=N and n>=j in lines 123–124.
Thus totalization outside the admissible eigenvalue range does not enter
the asymptotic estimate. Lines 126–134 cancel the full Taylor sum by the
triangle inequality. No extra d_(2m)(0) is missing or needs to be added.

This avoids the legacy trace-wrapper defect. No pair of incompatible
limits is assumed, and the proof does not ignore the hypothetical uniform
bound. The conclusion remains conditional, as required by manuscript
lines 345–355.

Scope is accurately limited: the result retains eta(0) in its limit.
To obtain the displayed manuscript constant, earlier work must establish
eta(0)=(m-1)*pi/2 and supply the actual Taylor/phase construction. The
absence of m>=3 from this scalar implication is harmless generality, not
a weakening of the canonical target. No theorem here constructs the
coefficient functions or establishes the spectral hypotheses.

## Numerical certification

Numerics.lean line 15 states exactly the selected margin

    1/4 < sin(pi/4).

Line 16 rewrites the trigonometric value using the exact Mathlib identity
sin(pi/4)=sqrt(2)/2. Lines 17–18 certify the single closed inequality
1<=sqrt(2); lines 19–20 use exact coercion and linear arithmetic to obtain
the strict margin. The rational annotation on the left side of the
certificate does not change the real comparison.

Kernel trust is explicit both globally at line 11 and at the certificate
call at line 18. There are no matrix-size computations, parameter boxes,
subdivisions, external floating-point premises, or repeated certificate
calls. The claimed result is the sign margin only, not Lemma 4's
root-existence, derivative, simplicity, or index-counting conclusions.

## Contract equality and trusted import boundary

All five theorem type signatures in Challenge.lean and Solution.lean
are identical after whitespace normalization, including every implicit
parameter, hypothesis, quantifier, exponent, and conclusion. A static
Python extraction of each theorem header through its proof delimiter
confirmed that equality. This is source-level evidence, not an
elaborated Comparator type comparison.

| Declaration in MF21Restart.Contracts | Challenge lines | Solution lines |
| --- | --- | --- |
| complex_fourier_eq_cosine | 13–18 | 12–17 |
| bulk_cutoff_pos | 20–22 | 19–21 |
| critical_bound_implies_fixed_index_limit | 24–38 | 23–37 |
| exists_log_sq_bulk_scale_gain | 40–46 | 39–45 |
| phase_window_margin | 48–49 | 47–48 |

The configured names in comparator.json are exactly these five names.
No contract claiming MF21Restart.Target is configured.

The import closure was inspected:

- Challenge imports only MF21Restart.Definitions.
- Solution imports MF21Restart, whose four project imports are
  StatementBridges, FixedIndex, BulkDecay, and Numerics.
- None of those modules or Definitions imports Challenge or Solution.
- The project declarations appearing in the contract types are all in
  the shared Definitions module; the other type-level declarations come
  from its Mathlib import closure.
- The contract namespace is distinct from the implementation theorem
  namespace, and every Solution proof explicitly names the implementation
  declaration.

Challenge's five deliberate placeholders remain solely on the challenge
side. No placeholder is in the solution import closure. No Comparator
definition holes are configured. The permitted axiom list is exactly
propext, Quot.sound, and Classical.choice; it does not include sorryAx
or a custom result axiom.

A source scan found no sorry, admit, custom axiom, unsafe, or native_decide
tokens in Solution.lean or its project import closure. The separate local
axiom reports below are stronger evidence for the compiled implementation
theorems than this text scan alone.

The StatementBridges contracts also correspond to their intended
source-fidelity obligations: lines 44–65 prove the literal normalized
complex Fourier identity using the odd sine integral, and lines 67–76
prove the positive log-squared ceiling for every natural n. These close
the two connecting lemmas recorded as pending in the earlier definitions
review.

## Local evidence inspected; Comparator remains unrun

At initial review, the coordinator's completed local record
20260920T122932972971Z reports seven successful serial module/audit
compilations. Its exact record SHA-256 is
f353da4f082bf1f3020729433d9d33b168ddd715305a257295d6c5c486d12833.

This reviewer recomputed and matched every source, log, and output hash
listed in that record. Each recorded compiler invocation uses
lake env lean -j1 -M4096, and each records LEAN_NUM_THREADS=1.
The retained Audit.log SHA-256 is
ceda464af9cc3d3ed7c01aac8aa7bdb597b717b2d6ee41f2dcc6861e1acbeee9.
Its eight implementation/helper reports contain only propext,
Classical.choice, and Quot.sound.

That initial run did not compile Challenge.lean or Solution.lean.
The coordinator subsequently added them to the serial local runner.
The completed final run is independently checked in the addendum below
and closes this local elaboration gap. The static contract approval above
is unchanged.

No GitHub Comparator, independent Comparator kernel replay, or sandbox
run has been inspected or claimed. The prepared five-contract
configuration must not be described as a Comparator pass. The full
original-target verification count remains zero.

## Final local-evidence addendum

The coordinator's final serial local run completed successfully:

- Record: evidence/runs/20260920T123258467923Z/record.json.
- Record SHA-256:
  15ef281248a099015d91151d3c795c54bd1cd7abad080e6b9778bd577ae15006.
- Started 2026-09-20 12:32:58.467923 UTC; finished
  2026-09-20 12:34:36.640322 UTC.
- Runner SHA-256:
  87bce2d6e1970fe2170b3b82f9d76ae42aa5273c7f31c4121953fc646ba89c90.

This reviewer independently read that dated record and recomputed the
record, runner, all nine source, all nine compiler log, all nine output,
and all three dependency-configuration hashes. Every hash matched.
The latest-local.json bytes equal this dated record. All reviewed proof
and contract sources still have the hashes listed above.

All nine exit codes are zero: Definitions, StatementBridges, FixedIndex,
BulkDecay, Numerics, MF21Restart, Solution, Challenge, and Audit.
Every recorded command uses one thread and a 4096 MiB limit, with
LEAN_NUM_THREADS=1. In particular, the contract-module commands were:

    lake env lean -j1 -M4096 -o .lake/build/lib/lean/Solution.olean Solution.lean
    lake env lean -j1 -M4096 -o .lake/build/lib/lean/Challenge.olean Challenge.lean

The updated runner verifies all recorded source and pin hashes again
after the serial compilation sequence. The record reports those checks
passed.

| Evidence | SHA-256 |
| --- | --- |
| Solution.log | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| Solution.olean | fedf348dc5cb269b87688eed16ebc5ed9fabf4223042f645ab3abe4e969a7e6f |
| Challenge.log | 4baabb0be3a0f329ed88cdbc915aa4feb792036b951f6017b5d54d778c78e7b4 |
| Challenge.olean | 01008bdf958c9c1893b980cf767042204734ef3ab745b7a932961c0699f29a1f |
| Audit.log | ceda464af9cc3d3ed7c01aac8aa7bdb597b717b2d6ee41f2dcc6861e1acbeee9 |

The final Audit.log contains exactly eight implementation/helper axiom
reports, all restricted to propext, Classical.choice, and Quot.sound.
Challenge.log contains the five expected placeholder warnings.
The five deliberate Challenge proof holes are at source lines
18, 22, 38, 46, and 49; they are excluded from proved results and are
not imported by Solution. No other sorry, admit, custom axiom, unsafe,
or native_decide occurrence was found in the reviewed solution-side
project sources.

The successful local elaboration of both modules supports the static
contract-design verdict. It does not perform Comparator's isolated
statement comparison, independent kernel replay, or sandbox checks.
The final record still correctly states comparator=not_run and
github_run_id=null. The full MF21Restart.Target remains unproved.

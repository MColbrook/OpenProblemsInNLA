# MF-14 final independent referee B

**Verdict: APPROVE.** No blocking finding in statement fidelity, mathematical proof correctness, generality, degenerate cases, reuse/API, documentation or attribution for the frozen degree-44 package. This is source-review approval, supported by authenticated **existing coordinator-owned macOS Lean evidence**. I did not run Lean, Lake, Comparator or a publication command. The required real GitHub non-root Linux Comparator/kernel/sandbox checks remain pending. This report adds **zero** to the completed-verification count and makes no new mathematical-resolution claim.

## Independence and exact scope

- Phase: final statement-and-proof review, 19 September 2026.
- Reviewer: `/root/nr04_mf14_final_referee_b`, an AI agent, wholly nonauthor of the MF14 definitions, statements, proof code and repairs. I have not authored or edited any Lean source and have not used the first final referee's report as evidence.
- Excluded proof authors: `/root` and `/root/recover_lean_sources`.
- Frozen packet: `.local-recovery-20260918/final-review-packets/MF14-v1`.
- `REVIEW-SNAPSHOT.json` SHA256: `e52fab5a7b58c3bc6fb2c2df1283d55c6e4352056689c900de936c12e2595436`.
- Statement freeze SHA256: `10d161750ec789b5b8f24e0e82e229a722017b77b4cb7bdce11787dde70d7e3c`.
- Exact per-file hashes, supplemental documents and evidence are recorded in `MANIFEST.json`. All 101 snapshot-listed file hashes match. The packet contains 87 Lean files, including the separate Challenge.

I started with the snapshot, complete canonical README and complete degree-44 mathematical source, then inspected the definitions, frozen contracts and proof chain. I read the substantive mathematical modules, the generated certificate structure and representative complete partitions, and exhaustively checked every remaining repetitive direction/column/row statement and proof shape with the referee-owned script retained here. That script also independently reconstructs the actual family derivative; its arithmetic is additional review evidence, never an input to the Lean proof.

The review applies the snapshot's `source-context/REVIEW-PROTOCOL.md` and pinned Tau Ceti review guidance at `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`, including correctness, proof quality, generality, reuse and attribution. It covers API, placement, naming and documentation under the NLA adaptation. This is not an official Tau Ceti service run, external human peer review or source-author endorsement.

## Original target and contracts

The unchanged original problem asks whether the greatest universally covered degree using at most seven products is 42. `NLA.MF14.Definitions` retains complex coefficients, initial availability of `1` and `X`, chronological products of two prior available linear combinations, a final free linear combination, and the full coefficient space `Fin 129 → ℂ`. `vanishingHull` quantifies all multivariate polynomial equations vanishing on the genuine output set; it is the affine complex Zariski closure intended by the source. `degreePlane` includes zero and every lower degree. `coveredDegrees` imposes the canonical bound 128.

`degree44_coverage : CoversDegree 44` is universal and unconditional. It supplies a covered degree strictly above 42, and `original_equality_false : ¬ IsGreatest coveredDegrees 42` therefore answers the unchanged original question negatively. The package does **not** prove the later stronger exact maximum 47, its upper bound, exact representation of every polynomial by seven products, or numerical stability. These exclusions do not weaken the negative answer to the original equality.

All 25 Challenge theorem signatures match exactly after whitespace/comment normalization with their unique implementation declarations. The configured theorem list is precisely those 25 contracts, with `definition_names = []`. No replaceable definition is admitted. Shared definitions are transparent mathematical data rather than the desired conclusions. The deliberate Challenge `sorry` bodies remain isolated: no implementation imports Challenge. A nested-comment-aware scan of every implementation found no `sorry`, `admit`, new `axiom`, `unsafe`, `native_decide`, `implemented_by` or `extern` token. The final declarations introduce no substantive hypothesis.

The chronological circuit model is not weakened by the fixed seven-gate representation. `CircuitFoundations` and `CircuitPrefix` prove the at-most-seven/exact-seven equivalence by padding with zero products and prove the degree bounds from the chronology. For four gates, every available output has degree at most 16 and the full 17-coefficient decode recovers it. Thus the joint space of four outputs has all 68 coefficients and has no unrecorded high terms.

## Critical proof bridges

### One circuit and the fourth-product image

`SimultaneouslyAvailable` requires a **single** prefix circuit for every member of the tuple. `ThreeProductTuple` constructs that common prefix, using `ThirdProductFactorization` and the proved nonzero denominator `gamma*s - 2*s^2`. `CircuitSpanOperations` proves that extending the prefix preserves previous available values. `FourthActualCircuit` appends the fourth product and preserves all three earlier outputs. The proof never combines four separately realizable polynomials as though they were jointly available.

`FourthSpanMembership` proves membership for all generator pairs and then uses the bilinear span API to cover arbitrary factor combinations. The twelve selected rows are `[0,1,2,3,4,5,6,8,9,10,12,16]`. `BasisDegreeData`, `SpanBasisCoordinates`, `SpanCoordinates` and `SpanReconstruction` prove that these rows determine the **entire polynomial** in the product span when `s ≠ 0`, using a triangular basis matrix with nonzero determinant. This is not a projection of the target.

`FourthJacobian` connects the actual Fréchet derivative to the displayed derivative columns. `FourthMinorCoefficients`, `FourthDeterminantBlocks`, `FourthMinorBlocks` and `FourthMinorIdentity` prove the exact minor

`(s^2)^5 * (lambda - eta - alpha*lambda*(gamma*s - s^2*lambda))`.

The identity holds for every complex parameter, including `s = 0`. The implementation reduces the determinant to identity/triangular blocks and a small five-by-five core; it does not enumerate a twelve-by-twelve determinant or assume nonsingularity. This differs from the pre-proof plan's suggested two-by-two final reduction, but proves the identical frozen contract with bounded exact algebra.

`PolynomialDensity` uses Mathlib's actual inverse function theorem to place an open neighborhood in the map's range, then `MvPolynomial.funext_set` on a product of infinite coordinate sets. Its dimension parameter is arbitrary, including zero. `JacobianEquivalence` identifies the matrix with `LinearMap.toMatrix'` of the actual derivative and uses determinant invertibility to construct a continuous linear equivalence. Smoothness is separately established. `FourthJointClosure` pulls back an arbitrary polynomial in **all 68 tuple coordinates** through the full-span reconstruction. Its witnesses are actual common circuits, so its density argument gives joint closure with the earlier outputs retained.

### Degeneration and exceptional parameters

`DegenerationCoefficientData`, `SyzygyExpansion`, the four `SyzygyMiddle` modules, `SyzygyFactors` and `SyzygyLowPart` discharge the exact whole-polynomial identity used by `DegenerationIdentity`. Coefficients 7 through 10 cancel; all coefficients through 16 are accounted for; no coefficient above 16 is discarded. `degenerationZ` is defined polynomially in `s`, rather than by a quotient whose value at zero is arbitrary.

`DegenerationAtZero` proves the exact value

`Z_0 = X^12 + C(3*alpha - 4*gamma^2)*X^11`.

`ProductSpan` justifies low-coefficient subtraction inside the span because every monomial through degree 6 belongs to that span; it then divides by `s^4` only under `s ≠ 0`. Low-part extraction is not introduced as a permitted circuit operation.

`GoodParameters` proves all required nonvanishing conditions eventually on the punctured neighborhood of zero for every fixed complex `alpha`, `eta` and `gamma`. It treats `gamma = 0` explicitly and handles `gamma ≠ 0` by continuity; the remaining minor factor tends to 1 at zero. No exceptional input survives as a final restriction.

`MonicBorderPath` constructs the needed sparse monic degree-12 family inside the span at nonzero parameters and proves its exact limit. `BorderPathContinuity` proves coefficientwise continuity, including all 68 tuple coordinates. `BorderLimit` uses closedness of the common polynomial zero sets, the punctured limit and existence of a complex square root to fit arbitrary `alpha`, `beta` and all seven `xi` parameters. The subtraction of `alpha*Q` and choice `eta = beta + alpha^2` give the intended limiting `R`. The conditional fourth-product closure premise in the helper is fully discharged by `FinalClosure`.

The border lemma is tailored to the sparse monic degree-12 family required by the final continuation. It need not assert the manuscript's stronger auxiliary forms: the ensuing 45-dimensional density argument proves universal degree-44 coverage, including all nonmonic, zero and lower-degree targets.

### Full ambient closure and actual 45-dimensional derivative

`ContinuationCircuit` appends exactly the displayed three products to the one shared four-gate prefix. `ContinuationPolynomialMaps` and `PolynomialMaps` express **every one of the 129 output coordinates** polynomially in all 68 inputs. `ContinuationClosure` pulls back any vanishing polynomial on the canonical 129-dimensional space. Actual four-gate tuples decode exactly, so their images are genuine seven-product outputs. This establishes transfer of the original closure without imposing a projected high-coefficient condition.

`DegreeBounds` gives degree at most 96 for continuation of an arbitrary decoded tuple and the sharper final degrees 17, 22 and 44. `FamilyDegreeBounds` proves the equality of the full family vector with `embed44 (coefficientMap theta)` from genuine vanishing of higher coefficients. `CoverageBridge` reconstructs each vector of the original degree-44 plane and pulls back an arbitrary full-space polynomial. The final density and family-image hypotheses are both proved inside `FinalClosure`.

`FirstDerivatives` proves compositional coefficientwise derivative rules for constants, actual parameters, sums and polynomial products. `PolyFirstJet` is data with a separately proved soundness predicate; no derivative assertion is true by definition. `FamilyFirstJet` constructs the jet of exactly `familyPolynomial`, proves its value and soundness, and derives the actual Jacobian using the standard coordinate basis. `SeedFirstPilot` and all `SeedFirstColumns` partitions prove the whole-polynomial directional identities at the prescribed base point. The parameter blocks are bounded contiguous `Fin` indices, so none wraps modulo 45. The one-valued indices are exactly 0, 22, 32, 34, 35 and 44.

`Mod3Columns0` through `Mod3Columns8` prove all integer polynomial expansions and match every table coefficient. `Mod3Rows0` through `Mod3Rows8` use `decide +kernel` on exact natural residues to check the entire inverse product. `Mod3CastBridge` proves the cast from those natural computations to `ZMod 3`. `Mod3Certificate` assembles all 45 column and row cases. `JacobianNonzero` uses the checked right inverse, determinant naturality under integer casts and injectivity of the integer-to-complex cast. `JacobianIdentity` connects that nonsingularity to the actual derivative. The proof needs, and proves, nonzero determinant; it does not claim the literal value 256.

My independent Python dual-number reconstruction of the original family matched **all 2,025 derivative entries** and verified **all 2,025 product entries** of the supplied inverse modulo 3. It checked all 45 sparse whole-polynomial column expansions and coefficient formulas, all 45 kernel-decision row shapes, and the 43 repetitive seed-direction proof shapes; the two pilot directions were read separately. Every reconstructed derivative direction has degree at most 44. This is an additional independent arithmetic check, not a substitute for the reviewed Lean derivative proof or a new Lean execution.

## Quality, reuse, API and documentation

The proof separates chronology, span coordinates, derivative soundness, polynomial density, degeneration, closure transfer and final coverage into explicit interfaces. The reusable density theorem covers any finite dimension without an unnecessary global polynomial-map assumption. Polynomial-map and coefficient-derivative helpers provide compositional APIs; final specialized constants correspond to the fixed construction rather than unjustified domain restrictions. Conditional assembly lemmas are documented as conditional and are not confused with the unconditional final theorems.

I searched the pinned Mathlib checkout at `0df444a360eaa60ab8c11dca51a86af692955474` in the multivariate-polynomial, analysis, inverse-function, span and matrix/determinant APIs. In particular, I inspected `MvPolynomial.funext_set`, `eval₂Hom_bind₁`, `HasStrictFDerivAt.toOpenPartialHomeomorph`, `LinearMap.BilinMap.apply_apply_mem_of_mem_span`, determinant casts and the right-inverse determinant API. The implementation uses these existing bridges. A bounded search for a direct polynomial-density/vanishing-closure inverse-function result found no replacement for the new short composite lemma. The bespoke circuit and coefficient-span constructions need the original problem's finite chronology and simultaneous tuple semantics. I found no concrete avoidable duplication that blocks approval; this is not an exhaustive search of all Mathlib.

I also inspected the archived Forsythe numerical-target and separate-Challenge examples and the relevant Schiffer Challenge setup as workflow/API patterns, without importing their mathematical results or relying on their verdicts. Exact data are transparent, the scalar fields and coefficient orders are documented, and kernel computation is limited to the consumed modular and symbolic certificates. No artificial interval certificate or unused numerical bound is introduced. Local `change`/coercion steps expose concrete evaluation or coordinate expressions and do not hide a change of mathematical target. The small generated partitions are justified by bounded kernel work and have exhaustive assembly checks.

The publication metadata and README correctly distinguish the original negative answer from the later exact-47 result and distinguish macOS local evidence from pending Linux checks. I checked that all 87 publication Lean files equal the frozen packet and that Lake dependency entries are unchanged. The publication top-level Lake manifest name is corrected to `NLAMF14Degree44`; the snapshot's copied `NLAPF03` name is packaging metadata, not a proof change. The historical pre-proof wording in `NUMERICAL_TARGETS.md` and Challenge is identified by the README as historical. One nonblocking bookkeeping item remains in the inspected `IMPLEMENTATION-MAP.json`: its `final_source_binding` text still says `PENDING coordinator completed closure`, although all 25 recorded source hashes already match. The coordinator was notified to refresh this status with the review integration.

Attribution is appropriate: Marcus Webb, The University of Manchester, retains the degree-44 mathematical construction; Matthew J. Colbrook, University of Cambridge, retains the earlier degree-42 result; George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, is credited for formalization and proof engineering. Substantial Codex/ChatGPT assistance, prior library authorship and Apache-2.0 licensing are disclosed. No email is published. The records do not claim author endorsement or official Tau Ceti review.

## Authenticated local evidence and remaining gate

I independently authenticated `verification/MF14-local-20260919/LOCAL-REPLAY-AUDIT.json`, SHA256 `94021fa538957ad35044b9a6540fecf8a3ca99bcacd6546881cd3ac1b37e2cfa`, against the frozen source and archived original receipts. Checks passed for 86 proof source/fresh-log records, 54 compressed and decompressed receipt hashes, and 662 reuse edges. Every recorded reused transitive source hash matched the snapshot, and every fresh-command dependency output hash matched the corresponding reviewed-source output record. Mixed receipts' other problems or failed commands were not treated as evidence for this proof. I did not re-execute the compiler or independently kernel-check archived object files.

The actual publication-name aggregate run is `recovery-088`. It used Lean 4.33.1 with `--threads=1 --memory=4096`, from the coordinator's `local-lean` directory, compiling `Solution.lean`; it exited 0 on 19 September 2026 at 07:51:43 UTC. The exact argv, working directory, times and resource record are retained in the audit. Its source SHA256 is `e5c888faffd3a0936d55c7cb9ec59d24ea54a60b204f921d5ee68734f5124d44`; log SHA256 is `4332f3f7259395d8785cf3877b763a6bb831f30ecd8a857ff131e6598b8a7336`; receipt SHA256 is `72478dd92a3bce17b57c7bda2834aaf57052ff35745826e86248e2610448015e`. I read its actual aggregate log and matched all 25 transitive axiom reports to the configured contracts and all 25 `#assert_trust kernel` commands. Only `propext`, `Classical.choice` and `Quot.sound` occur.

The same receipt records the separate exact-source Challenge elaboration after Solution, with exit 0. Its deliberate placeholders provide statement-elaboration evidence only. No standalone local Lake build, Comparator result or GitHub run is claimed by this report. Approval remains bound to the frozen Lean bytes; final Linux verification and subsequent evidence/status integration are still required before promoting completion.

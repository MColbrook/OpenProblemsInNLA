# Independent review: one actual uniform implicit phase

Verdict: **APPROVE** EtaNeighborhood, UniformImplicitScalar, and
ImplicitPhase at the exact hashes below. The chain constructs one
jointly analytic Y on a uniform open rectangle containing
`[0,pi] x {0}` and proves the actual equation, size bound, initial
value, and enlarged-interval uniqueness. The public actual-phase
theorem assumes none of those conclusions.

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. The
coordinator and the other source agent authored these modules. The
reviewer made no source edits and ran no compiler. Review follows the
pinned standards, SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact sources and actual local evidence

| Artifact | SHA256 |
|---|---|
| `UNIFORM_IMPLICIT_PHASE_STATEMENTS.md` | `27afcd0522a215ae389ee4cf17a91aba88553f76bb68d6f7f0e21237fce9e8b2` |
| `MF21Restart/EtaNeighborhood.lean` | `42e9f262613592e7a26cce34b6141725ff597f5ffa2d64d9c59b992311ccc36d` |
| `evidence/logs/eta-neighborhood-02.json` | `f18144245978262dc90d752b69bbe651d44672ae4760c685b8f405f1dcd77730` |
| `evidence/logs/eta-neighborhood-02.log` | `8ea56e628efc4d22693b0f3d4bce2328d3196e11edc5bfbc1133696fd1d343a1` |
| `.lake/build/lib/lean/MF21Restart/EtaNeighborhood.olean` | `64da5fe9c095ea4a103c75467d33f707677c80c804959747caf25d67d0d90973` |
| `MF21Restart/UniformImplicitScalar.lean` | `f29817992fac4a25a9c9df585b394db98f963d5a37e3a81538c1f7d3913dfc56` |
| `evidence/logs/uniform-implicit-scalar-01.json` | `020db46bbb26d0aa5bd86dc721c4cc29f6dec667d620f5deac35e14dda8a3fe7` |
| `evidence/logs/uniform-implicit-scalar-01.log` | `4c42fdcdfcf64977b2ea7c676fdf54810ae23eaa57fc69ad797d48ce3f31724b` |
| `.lake/build/lib/lean/MF21Restart/UniformImplicitScalar.olean` | `04c5f9a2c28b0d42d2404c31bb684fa4bb1dbc181d221869f11e511fb46fa403` |
| `MF21Restart/ImplicitPhase.lean` | `db3e9ecbaa3dac159bc6bd736363794cbeb09afeaa1fd815a8b3d959b093a1dc` |
| `evidence/logs/implicit-phase-01.json` | `bbd7247d18446bd951dc82674ba999c2bae434fc777ebcd2393085980898b764` |
| `evidence/logs/implicit-phase-01.log` | `dcf86b0142642a840b1c5b1872fec69d1a73e2a73fab7b1edb9b1245cb7ba749` |
| `.lake/build/lib/lean/MF21Restart/ImplicitPhase.olean` | `4beffbebbdabcce797cfb06ad4e6bd76e0bb6e2f07a0e4a9bc08dd881c59ce80` |

The reviewer independently recomputed all hashes and matched current
source, log, and compiled output to each recorded successful local run.
Each records `exit_code=0`, `source_unchanged=true`,
`LEAN_NUM_THREADS=1`, and the command
`lake env lean -j1 -M4096 -o
.lake/build/lib/lean/MF21Restart/<Module>.olean MF21Restart/<Module>.lean`.
Each module has one printed public axiom report, containing only
`propext`, `Classical.choice`, and `Quot.sound`. The scalar module has
one unused `ext` pattern warning at line 152; it is optional cleanup,
not a missing proof or correctness issue. Comparator has not run.

The unchanged manuscript `original-proof/solution.md`, SHA256
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`,
has the relevant actual equation and neighborhood construction at
lines 52–56, regular phase at lines 77–82, and the uniform-smoothness
input to Taylor expansion at lines 280–286.

## Statement fidelity and analytic order

1. `ImplicitPhase.lean:18–27` matches the five promised conclusions
   in the shared statement lock. The order of quantifiers supplies
   positive r,epsilon,C and one function Y for each m>=1, followed by
   every point of the fixed open rectangle. Its x interval extends
   past both 0 and pi; the h interval includes both signs. The fixed
   root-uniqueness interval is the larger closed `[-r,pi+r]`.
   The phase equation is `Y=x+h*manuscriptEta m Y`, with the same
   plus sign as manuscript (4). There is no dependence on matrix
   size or eigenvalue index in the selected Y or constants.

2. The pinned Mathlib uses `ContDiff` order `ℕ∞ω=WithTop ℕ∞`, with
   `⊤` denoting omega and the coerced ENat top denoting infinity:
   `Mathlib/Analysis/Calculus/ContDiff/Defs.lean:90–91,119–134,927–938`.
   Its `ContDiffAt.analyticAt` at lines 978–981 confirms the analytic
   conclusion. `ContDiffAt.eventually` at lines 1036–1040 requires
   the order to differ from infinity. EtaNeighborhood applies it at
   omega and discharges that requirement. It does not infer an open
   smooth locus from arbitrary C-infinity-at-a-point hypotheses.
   The stronger analytic input already follows from the existing
   literal `manuscriptEta_contDiffAt` (`PhaseZero.lean:96–101`);
   no new extension or branch is assumed for this chain.

## EtaNeighborhood proof findings

3. At lines 25–59, U is the analytic locus of the already defined
   actual eta on the real line. U contains `[0,pi]`, is open at
   analytic order, and has positive-radius neighborhoods at both
   endpoints. Choosing r as half the minimum endpoint radius puts
   the entire enlarged closed interval in U: points inside `[0,pi]`
   use the original theorem, and exterior pieces use the respective
   endpoint balls. This is an actual uniform enlargement, not a
   collection of incompatible pointwise neighborhoods.

4. At lines 60–85, actual analytic regularity supplies continuity
   of eta and of its ordinary derivative on the enlargement. Compact
   bounds for both functions are combined by `max(max(C1,C2),1)`.
   The resulting C is positive and controls both absolute values
   at every point of the same closed interval, including both new
   endpoints. No derivative bound is left as an actual-phase premise.

## UniformImplicitScalar proof findings

5. Lines 25–36 impose only analytic regularity and explicit finite
   value/derivative bounds for a generic eta on `[-r,L+r]`, where
   L>=0,r>0,C>0. These are natural sufficient hypotheses and are all
   later discharged. No solution function, root, inverse map, or
   derivative invertibility is assumed. L=0 is allowed and the
   enlarged interval still has positive width.

6. Lines 38–74 choose `epsilon=min(r/4,1/2)/C>0`. For either sign
   of h in the open range, `|h|*C<r/4` and `<1/2`. Hence
   `1-h*eta'(y)>0` uniformly throughout the enlarged interval.
   Strict monotonicity is proved for `y-h*eta(y)` by the derivative
   theorem and actual differentiability. This gives uniqueness on
   the full fixed interval, not merely an eventual neighborhood.

7. Lines 75–107 prove existence **before** invoking the implicit
   function theorem. The endpoint perturbations have magnitude
   less than r/4, while x stays between `-r/2` and `L+r/2`, so the
   two endpoint values strictly bracket x. IVT on the closed
   interval yields a root; strict monotonicity proves its uniqueness.
   Lines 108–127 choose this unique root on the rectangle, define an
   irrelevant total value outside it, prove `|Y-x|<=C*|h|`, and use
   that displacement to place Y strictly inside `(-r,L+r)`.

8. Lines 129–154 apply the local implicit function theorem to the
   literal map `F((x,h),y)=y-x-h*eta(y)` at the already constructed
   root. Analytic composition proves regularity of F. Its actual
   partial derivative in y is identified, by uniqueness of the
   derivative, with scalar multiplication by `1-h*eta'(Y)>0`.
   The continuous linear equivalence for this nonzero scalar proves
   invertibility. The positive scalar is not merely assumed in a
   typeclass or imported hypothesis.

9. Lines 155–173 identify the local implicit function phi with the
   chosen Y on an open neighborhood. The library supplies phi(p)=Y(p),
   analyticity, and the eventual equation at the level F(p,Y(p)).
   The latter level is shown to be zero using the actual root
   equation. Continuity keeps phi in the enlarged interior and the
   open parameter rectangle keeps q in the global construction's
   domain. The previously proved enlarged-interval uniqueness then
   forces phi(q)=Y(q), yielding eventual equality and the claimed
   analytic regularity of that same Y. No continuity of the
   pointwise choice is assumed, and separate local choices are not
   silently glued without an equality argument.

10. Lines 174–179 return the already proved interior location,
    equation and displacement bound. At h=0 the actual equation
    gives `Y(x,0)=x`; no approximate initial condition is used.
    The value outside the rectangle is not claimed to be continuous
    or to solve the equation. `ImplicitPhase.lean:28–31` instantiates
    every scalar hypothesis with the proved actual eta enlargement
    and pi>=0, leaving only the intended m>=1 premise.

## Trust, documentation and limits

Recursive project-import scans contain 10, one, and 12 files for the
three reviewed modules, respectively, and found no `sorry`, `admit`,
custom `axiom`, `unsafe`, or `native_decide` marker. Challenge and its
five deliberate placeholders are outside these closures. The three
source-matched local axiom reports contain no additional trusted axiom.
This report independently reviews these three new modules, not every
previous helper in their import closures and not any code written by
this reviewer.

One harmless documentation discrepancy is already recorded in the
lock's explicit post-test erratum at lines 95–100: the frozen
ImplicitPhase module comment says equation (5), whereas the implicit
equation is (4) and (5) defines the coefficients. The actual equation,
statement lock, and theorem are correct; the source was not edited
after testing. Correcting this comment later requires a new recorded
source-matched run if its previous source hash is to be replaced.

This chain supplies the genuine uniform implicit-function input. It
does not yet identify Y at the spectral grid with the exact phase
preimage, prove the uniform Taylor remainder or coefficient vanishing
orders, or complete the original MF-21 Target. No complete-target
count changes. No material correctness or fidelity issue was found.

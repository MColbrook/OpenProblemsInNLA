# Independent review: scaled inverse integrand and cell estimate

Verdict: **APPROVE** the nine ScaledRising results and the single
RiemannCellBound result at the exact hashes below. They establish
concrete polynomial scaling and compact regularity of the inverse
integrand, plus a finite generic Riemann-sum error estimate. They do
not establish the inverse-kernel convergence in manuscript (26).

Reviewer: `/root/mf21_restart_lean_audit`, 20 September 2026. The
coordinator authored these sources. The reviewer did not edit them or
run a compiler. The pinned referee standards have SHA256
`e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1`.

## Exact sources and actual local evidence

| Artifact | SHA256 |
|---|---|
| `MF21Restart/ScaledRising.lean` | `23575eba296f34e65d9d5fc952bd707f64415206ad79488a06772e3c1313ac4f` |
| `SCALED_RISING_STATEMENTS.md` | `842b4714cd73c9f73f33a0ecb7df55f2e8b1822872954f7baeeb4c9fc89043a5` |
| `evidence/logs/scaled-rising-02.json` | `f54a399a8b80b3dbbcd40a7f034b07af9e536d5c379be2ada04354295ef14963` |
| `evidence/logs/scaled-rising-02.log` | `948c82cb1bd6bc4e717afcfc8e237efb0d7cb980d93c9ee9c5c60492eba9ac91` |
| `.lake/build/lib/lean/MF21Restart/ScaledRising.olean` | `6f44b8cdf6d21d75737d98db8bad890a77596e16ff3e8d754ca05cfc0e915d8d` |
| `MF21Restart/RiemannCellBound.lean` | `36df748366656ab16d28493d9d9e60ca4b3aa509a975b64286f86374da88e8f9` |
| `RIEMANN_CELL_BOUND_STATEMENTS.md` | `439b80a585d87c6f10c5c0e7ec85e2df5a888673dcb8b696b389da9092f7c53c` |
| `evidence/logs/riemann-cell-bound-03.json` | `7786264354fbc808243405b7525b0cd0ec1741a5f45256fbe6b06cff8b100903` |
| `evidence/logs/riemann-cell-bound-03.log` | `abdf89154870200196aeb5f343a04dcecf8d08bbcc951160f0539afe3d9d611d` |
| `.lake/build/lib/lean/MF21Restart/RiemannCellBound.olean` | `4df46444263f67b3a01c1bf616851de22072701d0e9eb6c20965d1d05ad2294e` |

All hashes were independently recomputed and match the stated successful
02 and 03 execution records, including current source, log, and output.
Both record `exit_code=0`, `source_unchanged=true`, `LEAN_NUM_THREADS=1`,
and `lake env lean -j1 -M4096 -o
.lake/build/lib/lean/MF21Restart/<Module>.olean MF21Restart/<Module>.lean`.
The logs have nine and one axiom reports, respectively, all limited to
`propext`, `Classical.choice`, and `Quot.sound`, and no error or missing
proof warning. Earlier unsuccessful test numbers are not substituted
for these actual successful runs. Comparator has not run.

The unchanged manuscript SHA256 is
`6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`.
The intended application is its lines 312–325, especially the exact
integrand in (27). The finite inverse supplying the rising products is
`InverseKernelEntries.lean:25–44`, independently reviewed separately.
Known Duduchava–Roch attribution for that inverse is unchanged.

## ScaledRising findings

1. **The finite polynomial has the right starts and degrees.** Lines
   15–32 define exactly `product a<r, (x+a*h)` and prove the successor,
   h=0, and scaling identities. The scale factor is h^r and the
   unscaled factor is the ascending Pochhammer polynomial of order r
   evaluated at x. There is no division by h, so h=0 and r=0 are
   included correctly. The order-zero product and power are both one.

2. **Continuity and positivity are derived.** Lines 34–46 prove
   continuity under arbitrary continuous real substitutions using the
   finite polynomial, and positivity from h>=0,x>0 term by term.
   Positivity is not asserted for a negative start or negative h.
   The theorem includes r=0, where the positive empty product is one.

3. **The concrete integrand retains every finite offset.** Lines
   48–57 have orders m,m,m-1,m-1 in the numerator, the starts
   `x,y,t-x+h,t-y+h`, and the denominator `((m-1)!)^2` times the
   order-2m rise at t. For one-based grid locations x=h*i,y=h*j,t=h*k,
   the shifted starts are h*(k-i+1),h*(k-j+1), matching the exact
   finite inverse. The h=0 identity is precisely the integrand in
   (27), with the external x^m*y^m/factorial-square incorporated
   into the integrand. The square and both m-1 exponents are present.
   Natural truncation at m=0 is harmless for these polynomial
   identities; it is not asserted to give the positive-order Green
   kernel. Real division is totalized, and no continuity is claimed
   at a zero denominator outside the specified box.

4. **The compact box is literal and stays away from the singularity.**
   Lines 59–80 use coordinates `(h,x,y,t)` in
   `[0,1]^3 x [1/4,1]`. The numerator is continuous without any
   sign restriction on t-x+h or t-y+h. The denominator is strictly
   positive from h>=0,t>=1/4>0 and factorial positivity, for every
   natural m. Hence quotient continuity is proved throughout the
   full box, including h=0. No ordering t>=max(x,y) is needed for
   continuity; the future integral application must impose its own
   lower limit.

5. **Uniformity follows from compactness, not pointwise estimates.**
   Lines 82–98 apply Heine–Cantor and a compact-image bound to that
   same four-variable function. The positive C in the bound depends
   on m, not on h,x,y,t. Replacing an arbitrary compact bound C by
   max(C,0)+1 gives strict positivity without changing the domain.
   This proves usable uniform regularity but no rate and no Riemann
   limit by itself.

## RiemannCellBound findings

1. **The public estimate matches its lock exactly.** Lines 15–23
   allow a monotone real partition, natural L<=U, interval
   integrability on each included cell, and a bound epsilon on the
   difference from that cell's right endpoint throughout the closed
   cell. The sum ranges over `Ico L U`, uses the actual length
   `a(k+1)-a(k)`, and is compared with the oriented integral from
   a(L) to a(U). The total length on the right is a(U)-a(L), with no
   extra factor for the number of cells.

2. **The cell proof controls an integral, not a finite sample.**
   Lines 24–42 apply the interval integral norm bound to
   `f(a(k+1))-f(x)`, use monotonicity to identify the unoriented
   interval and nonnegative length, and rewrite the integral of the
   difference using the stated integrability of f. The oscillation
   hypothesis is used for all points in the interval, so no numerical
   sampling is promoted to an analytic conclusion.

3. **The finite gluing and endpoint cases are correct.** Lines 43–56
   apply the adjacent-interval integral identity, the triangle
   inequality for the finite sum, and the exact telescoping length
   sum. L=U gives the empty sum and zero integral. Repeated partition
   points give zero-length cells and are permitted. No separate
   epsilon>=0 premise is necessary: a nonempty included closed cell
   forces it via the oscillation bound at its endpoint; for an empty
   index range the right side is epsilon*0 regardless of its sign.
   Global monotonicity of a is a convenient sufficient assumption
   satisfied by the intended uniform grid, not an impossible or
   circular spectral assumption.

## Trust, independence and remaining work

The project import closures contain 13 files for ScaledRising and one
for RiemannCellBound, including each reviewed module. Static scans
found no `sorry`, `admit`, custom `axiom`, `unsafe`, or `native_decide`.
Challenge and its five deliberate placeholders are not imported.
No new numerical certification is needed or introduced.

The reviewer authored some imported inverse infrastructure, including
WeightedBinomialInverse, FourierBinomialStencil and
ToeplitzWeightedFactorization. This report does **not** independently
review those proof internals; the approval concerns the two named
coordinator-authored modules and their faithful use of the already
stated finite inverse API. The source-matched local axiom reports cover
their complete used dependency closures without extra axioms.

The actual rescaled inverse-to-sum equality, shrinking-cell estimates,
moving lower endpoint, reflected portion of the square, and endpoint
index convention must still be assembled to prove (26). These modules
do not claim trace convergence, an asymptotic coefficient expansion,
or the original MF-21 Target. No completed-target count changes. No
material correctness or fidelity issue was found.

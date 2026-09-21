# Independent referee B: actual inverse-kernel uniform-limit chain

Verdict: **APPROVE within the exact scope below.** No material mathematical or statement-fidelity issue found. This is an independent source review of coordinator-authored components, not a compiler run by this referee.

The reviewed source is the frozen MF-21 manuscript at /private/tmp/mf21-solution.md, SHA-256 6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa, equations (26)-(29), manuscript lines 312-342. The rubric is /Users/georgestepaniants/Research/project/lean-verification/REFEREE_STANDARDS.md, SHA-256 e4771ab0a1c2f51541a2b849ec82fadaf7fc927ba4984295d25b08995d1947f1.

## Reviewed statements and proof dependencies

I read the nine complete sources listed below and their prior statement locks. I additionally checked the concrete definitions and interfaces in ScaledRising, ScaledInverseSum, and InverseKernelEntries to trace the conclusions back to the unchanged integral-defined Toeplitz matrix. The previously independently reviewed proofs of ScaledRising, RiemannCellBound, and ScaledInverseSum are relied upon; this report does not repeat those entire dependency reviews. In particular, no convergence assumption is hidden in finiteKernelIntegrand or the exact inverse identity.

1. KernelRiemannApprox proves uniform h-to-zero continuity and right-endpoint Riemann approximation for the actual finiteKernelIntegrand. The single compact box is h,x,y in [0,1], t in [1/4,1]. The threshold is independent of h,x,y and the moving lower index a. The cell sum covers k=a,...,n-1; the length of the whole integration interval is at most one. Empty sums at a=n are included. The epsilon bounds come from compact uniform continuity and the earlier symbolic cell estimate, without numerical enumeration.
2. KernelShiftedSum specializes h=1/n and separately controls the right-sum error, the integrand replacement F(h)-F(0), and the lower-endpoint displacement b-a/n. Each term is bounded by epsilon/3. All integrability obligations are supplied from continuity on the same nonsingular t interval; b=a/n or b=1 causes no exception. Its threshold is uniform in x,y,a,b.
3. InverseKernelGridTop defines X(n,i)=(i.val+1)/n and traces the sum to (toeplitz m n)^-1, rather than to an abstract matrix or an assumed approximation. The guarded Fin sum is exactly the natural range Ico(max i.val j.val,n). Thus the Riemann interval starts at a/n, whereas max(Xi,Xj)=(a+1)/n. The proof retains this first one-cell shift and applies the shifted-endpoint bound. Upper-half geometry gives max(Xi,Xj)>=1/2 and a/n>=1/2-1/n>=1/4 for n>=4. The last index and the zero-length limiting integral are covered.
4. InverseKernelContinuity constructs a globally continuous extension of the upper formula by replacing only t with max(t,1/4) inside the integrand. On x+y>=1 the complete interval between max(x,y) and 1 lies above 1/2, so the extension is proved equal to the actual unclamped upper integral. The limit integrand, by finiteKernelIntegrand_zero_step, is exactly x^m y^m (t-x)^(m-1)(t-y)^(m-1) / (((m-1)!)^2 t^(2m)); the manuscript's constant prefactor is placed inside the integral. At x+y=1, reflection swaps x and y, and the proved exact symmetry of the integrand makes the two branches agree. This proves gluing, continuity, and exact reflection, including all corners. No Green-operator identity or assumed convergence theorem is used.
5. InverseKernelGrid proves the second one-cell shift exactly: X(n,i.rev)=1-X(n,i)+1/n. Both reflected coordinates have that same displacement. The actual inverse is invariant under simultaneous index reversal. In the lower half, reversed grid points lie in the upper half, while the exact reflected continuous point is at sup-distance 1/n. Uniform continuity of the assembled kernel controls this displacement; exact kernel reflection then gives the desired value. No exact discrete-continuous reflection equality is substituted incorrectly.
6. InverseKernelLimit uses min(ceil(n*x)-1,n-1) as a zero-based Fin n index. On [0,1] the upper clamp is redundant; x=0 is separately treated and selects the first entry, x=1 selects the last entry. The one-based grid point lies between x and x+1/n in every case. The actual step kernel has factor (1/n)^(2m-1), which equals the manuscript's n^(1-2m) for n>0,m>=1. The final quantifiers are: for each fixed m>=1 and epsilon>0, one N>=4 works for every n>=N and every pair x,y in the closed unit square. No x,y-dependent threshold remains. The proof combines the all-grid estimate with uniform continuity of the concrete kernel. It proves a pointwise-uniform statement, stronger than the essential-uniform assertion (26), and directly includes the diagonal.

7. ActualKernelDiagonal applies the already checked substitution to the actual upper-half kernel, after explicitly pulling out the correct factor x^m*x^m/((m-1)!)^2. Reflection covers x<1/2 and includes x=0 by reflecting to 1. The resulting closed form is exactly (28), with exponent 2m-1 and denominator (2m-1)((m-1)!)^2. Integration uses the previously checked scalar beta identity and gives exactly the positive rational number in (29). This review independently covers the new bridge, its range, and its formula; it does not present this referee's earlier KernelDiagonal or TraceIntegral proofs as independently reviewed here. Their independent dependency reviews and local tests remain separate evidence.
8. GridAverage proves the actual right-grid average convergence for any continuous function on [0,1], with the same (i+1)/n grid and both endpoints covered by cell integrability. It derives the quadrature error from compact uniform continuity and RiemannCellBound. It does not assume the desired limit or a quadrature bound. Its eventual n>=1 avoids the irrelevant totalized n=0 case.
9. ActualTraceLimit first proves the exact finite scaling identity: n^(-2m) trace(A^-1) equals (1/n) times the sum of n^(1-2m)-scaled diagonal entries. The uniform diagonal error therefore averages to epsilon/2 rather than growing with n. The actual continuous diagonal average converges by GridAverage, and the previously established diagonal integral supplies the explicit constant. Finally, multiplication by (n/(n+2))^(2m), which tends to one, proves precisely the manuscript's (n+2)^(-2m) normalization. The algebraic cancellation is restricted eventually to n>=1. Neither trace convergence nor a spectral trace identity is assumed.

## Trust and evidence

No sorry, admit, custom axiom, unsafe shortcut, native decision procedure, or unproved limiting hypothesis occurs in the nine reviewed sources. They contain 31 reported declarations in total. I read the actual retained JSON records and logs, and independently recomputed the hashes of every reviewed source, statement lock, JSON record, log, and current output olean. All nine records have exit_code=0, source_unchanged=true, and exact matching source/log/output hashes. All 31 axiom reports list only propext, Classical.choice, and Quot.sound. The grid/limit logs have harmless unused/unreachable ring-tactic warnings; ActualKernelDiagonal has a harmless redundant-change warning.

The recorded command for each module is:

    env LEAN_NUM_THREADS=1 lake env lean -j1 -M4096 -o .lake/build/lib/lean/MF21Restart/<Module>.olean MF21Restart/<Module>.lean

The working directory is the MF21-restart project. These are actual coordinator local tests whose retained evidence I inspected; I did not start a compiler. No GitHub Comparator run is claimed.

## Scope boundary

This report approves the concrete full-square uniform inverse-kernel limit, its explicit reflected integral formula, the bridge to the diagonal closed form, and the actual trace limit (29). It does not claim a formal differential-operator/Green-function characterization, the trace identity as reciprocal sorted eigenvalues, the dominated spectral trace limit (31), the original three-part Target, or final Comparator acceptance. Those are separate obligations. The manuscript is unchanged.

## Exact source and evidence hashes


### kernel-riemann-approx-02

- Source: `MF21Restart/KernelRiemannApprox.lean`; SHA-256 `13904889aaecd28e76a655240807b177aa45844bd8de2de32eaed1d002efcb19`.
- Statement lock: `KERNEL_RIEMANN_APPROX_STATEMENTS.md`; SHA-256 `b33d7372597e34ccf70bfae246b87503bbb84f0269aa9302a4a9630fc6eafa1d`.
- Record: `evidence/logs/kernel-riemann-approx-02.json`; SHA-256 `88e0a9fa3da518f1fd4095ba8740fa5641f09b8f659e55f4acd0eda77cb944f8`.
- Log: `evidence/logs/kernel-riemann-approx-02.log`; SHA-256 `f09f1df9d8c1f08d0f697a1f3462b06e86de4c0e2a9c594c0f729ea77dd745ff`.
- Output: `.lake/build/lib/lean/MF21Restart/KernelRiemannApprox.olean`; SHA-256 `d27d2a2643466d34aae20963967bc3c2ad3b8a4b5ecbc84e654b26da6d13b1bb`.

### kernel-shifted-sum-01

- Source: `MF21Restart/KernelShiftedSum.lean`; SHA-256 `d59239301b9a0db3b55a7c2e3e0ffcfbcd9a64936823b55ee0591c04f9e4091c`.
- Statement lock: `KERNEL_SHIFTED_SUM_STATEMENTS.md`; SHA-256 `dcbe3a2b01175888f5c2eaa295ca43c15d1d043b8105d1b0347a20a5e2dba11a`.
- Record: `evidence/logs/kernel-shifted-sum-01.json`; SHA-256 `a288b9292b5c56e7c8c5d6cf696503112400d993b5074cd686b0c9c59ef5a991`.
- Log: `evidence/logs/kernel-shifted-sum-01.log`; SHA-256 `d71f67c8ea6b23e02188a500530f6a2dba08663b8b8cd510b4a85a88b6ae9beb`.
- Output: `.lake/build/lib/lean/MF21Restart/KernelShiftedSum.olean`; SHA-256 `7cef7bc8bca121c3e957f9af40b52a2b0bc67eb6389767fef85bbead2d09a416`.

### inverse-kernel-grid-top-01

- Source: `MF21Restart/InverseKernelGridTop.lean`; SHA-256 `b323ba3ed3af5e51044ca6af6b8a96cef70481cd70bf3dc3c22c438563de1b2a`.
- Statement lock: `INVERSE_KERNEL_GRID_TOP_STATEMENTS.md`; SHA-256 `1ff3b4e33e219fc114b20713b3aed992ece37e31420f5fad02a97decd8a11bce`.
- Record: `evidence/logs/inverse-kernel-grid-top-01.json`; SHA-256 `df55232ef647057fe99d2480ae41ffac9866101073ddbe6ab5e436e4194c09e0`.
- Log: `evidence/logs/inverse-kernel-grid-top-01.log`; SHA-256 `80161f62dc160dd56e071e845670de7ba96f9c9d5cb1e36628a98cb6b87db84c`.
- Output: `.lake/build/lib/lean/MF21Restart/InverseKernelGridTop.olean`; SHA-256 `e4011dfafe566144e2b0d90c6c9a276a5c00c0c707f84d6f6ac5b192fed98257`.

### inverse-kernel-continuity-02

- Source: `MF21Restart/InverseKernelContinuity.lean`; SHA-256 `63299f9afc95a00d783086a93cf6dc9205790d7fefbc6b4312b02526a05f7e4d`.
- Statement lock: `INVERSE_KERNEL_CONTINUITY_STATEMENTS.md`; SHA-256 `b1640f4abf39e81b2bcfa7493b53533a16adfecd663937219de79d2fc6d8b7fa`.
- Record: `evidence/logs/inverse-kernel-continuity-02.json`; SHA-256 `f58630e7fe1400fc86a1da8acc1aa8be10c2a83dffbd43406f265c3a0e3ecdd3`.
- Log: `evidence/logs/inverse-kernel-continuity-02.log`; SHA-256 `c7c502d66c46bf6d0ab9f1fd3164eeb056b11c0e8ea84fc7a2932341ec0f324a`.
- Output: `.lake/build/lib/lean/MF21Restart/InverseKernelContinuity.olean`; SHA-256 `88483b4447da6c0b5e99afc39352b647e89f33780a2768049adf2ee5b7877b1e`.

### inverse-kernel-grid-02

- Source: `MF21Restart/InverseKernelGrid.lean`; SHA-256 `48629ecc6165f1343374ad5f20b3805cdd88c2f17441039fba2308bf2864afc9`.
- Statement lock: `INVERSE_KERNEL_GRID_STATEMENTS.md`; SHA-256 `4c0372899ae0d37bd6ef704e03b302a2e9532b69a05c65c338f9633de972cc4d`.
- Record: `evidence/logs/inverse-kernel-grid-02.json`; SHA-256 `ef5862f0705eabc3aead688a35c9bd57acdf9f153190cd9aa4de79882c65b677`.
- Log: `evidence/logs/inverse-kernel-grid-02.log`; SHA-256 `1675984c8de28c01408deff64b2117e503f05ec28b3a357d588f779b865c3f0f`.
- Output: `.lake/build/lib/lean/MF21Restart/InverseKernelGrid.olean`; SHA-256 `e2bef800a7fe90a2eae4296e4a6871aff7268e623850b13d93bdc7f44a4c5ece`.

### inverse-kernel-limit-01

- Source: `MF21Restart/InverseKernelLimit.lean`; SHA-256 `e7a8f48440570bb2ca8d62c770d252618e3d4eeaecc1daceed254255282e5ea9`.
- Statement lock: `INVERSE_KERNEL_LIMIT_STATEMENTS.md`; SHA-256 `b54d3343e67c54bd4f43eabdda8e5685036bd319123bb64cf40edd3060c9c0a6`.
- Record: `evidence/logs/inverse-kernel-limit-01.json`; SHA-256 `b28400e622fb4d7885e9f109763af259924df78406883a47e3584967134b8f26`.
- Log: `evidence/logs/inverse-kernel-limit-01.log`; SHA-256 `dcf2d3f014313682e71f846eeb516a8ce2b11e9496c47df56c261ae5112a6203`.
- Output: `.lake/build/lib/lean/MF21Restart/InverseKernelLimit.olean`; SHA-256 `23334f1a2ab58c1bcab863214789fb7f987fa67a41e0f8f7c9cdbe2209532b95`.

### actual-kernel-diagonal-01

- Source: `MF21Restart/ActualKernelDiagonal.lean`; SHA-256 `6deda38f66840d6e29a073a890ad288b931d346e483b44aee2f90963b6e3c81c`.
- Statement lock: `ACTUAL_KERNEL_DIAGONAL_STATEMENTS.md`; SHA-256 `2d3d2fe7835b895180d01339d8d21c0bef4e1125d5d5736d288ba7eb689d21b5`.
- Record: `evidence/logs/actual-kernel-diagonal-01.json`; SHA-256 `6e30e8eb08155f04fcec91adfaad7405d9cdaa941f625591b6798fc7586fdc1b`.
- Log: `evidence/logs/actual-kernel-diagonal-01.log`; SHA-256 `b87411680f9aa1fdfd5844fec34214db121ef479db63fdfc1b202720441b2141`.
- Output: `.lake/build/lib/lean/MF21Restart/ActualKernelDiagonal.olean`; SHA-256 `96538f730b167ce27c9ee025a7ccc9cd3548eb73d70cad75838a75113111a921`.

### grid-average-03

- Source: `MF21Restart/GridAverage.lean`; SHA-256 `fd663995c60719cf9245eeba5c7fc728ea51ac7c1eb2d903f789b5b5368fa498`.
- Statement lock: `GRID_AVERAGE_STATEMENTS.md`; SHA-256 `80ae0a5f5d15909941c0f1285aacbbad6df707a4631022a18458f7da4b693cd4`.
- Record: `evidence/logs/grid-average-03.json`; SHA-256 `e44521635b17e0f4810420c56a0aa829619b63564256487b66009deab93421da`.
- Log: `evidence/logs/grid-average-03.log`; SHA-256 `9b22f8c0cba056e951d4e34b886e2c92e3588fee95abbaf4352ff6d3ffe0d7e8`.
- Output: `.lake/build/lib/lean/MF21Restart/GridAverage.olean`; SHA-256 `936f1082394a0873aa29aa63f20ecc25f25b4dd52c6563b4ef1b4a63fc5a78c6`.

### actual-trace-limit-02

- Source: `MF21Restart/ActualTraceLimit.lean`; SHA-256 `192550076632c3ac021957564d7717b5300e0451de69301aee308ab58dd7473e`.
- Statement lock: `ACTUAL_TRACE_LIMIT_STATEMENTS.md`; SHA-256 `c22558ddbce123314102203e1735fa97e3b0f74ec48c132777472cf189c81d01`.
- Record: `evidence/logs/actual-trace-limit-02.json`; SHA-256 `eeaaf1cb4a3acc830cc6a9119686af5bbc0f374d6d0b3a6ef3d4d6dd421e8dd7`.
- Log: `evidence/logs/actual-trace-limit-02.log`; SHA-256 `e185d85e66e9f027eeeec39e783f755dc9034dc1986a8723770f69af7a1bbd8f`.
- Output: `.lake/build/lib/lean/MF21Restart/ActualTraceLimit.olean`; SHA-256 `4026aa94612aa16316bc1956a5ba3b2c664e041dbda43dc206723de30a21f87b`.

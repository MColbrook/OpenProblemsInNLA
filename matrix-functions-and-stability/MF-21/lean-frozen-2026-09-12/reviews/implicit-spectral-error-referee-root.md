# Independent source review: actual implicit spectral error

Reviewer: coordinator/root. Verdict: APPROVE within the scope below.

The three proofs were authored by mf21_restart_manuscript. Root made only
an elaboration repair (`simp only [id_eq]`) in the symbol derivative after
its first failed local test, and ran the serial compiler. This is independent
mathematical/source review of the agent-authored argument, not independent
execution or review of root's own compiler orchestration. No Comparator
result or full Target approval is claimed.

Reviewed evidence (actual successful local runs, recomputed hashes):

- `MF21Restart/SymbolDerivative.lean` source `ae15318c03af3eaa7060a50b9b47206450575cd934c8f93d420bc57e0b934519`; record `evidence/logs/symbol-derivative-02.json` SHA `55c8bd8c554e22e1ac4aac936115e63473f69a702f5e6c1c61088f4183b25dbf`.
- `MF21Restart/ImplicitSpectralError.lean` source `41da02350921c1a6e8cfae0c366ab1801e549c10d554752083f567705566cf2e`; record `evidence/logs/implicit-spectral-error-01.json` SHA `1ee3948570aac82410142256f8d72f966a756a41a4c84c7fa21b55601eb03b8b`.
- `MF21Restart/ImplicitSpectralData.lean` source `e379ad2cfd444ba82aa0f10e9c4d51c2bf61d081836754c24ae7c2029fd1bc1b`; record `evidence/logs/implicit-spectral-data-01.json` SHA `dde63d27bcc87cc623d92566043492ecb61a76e1cb1696065bc5e4399899088e`.

The printed reports are three, two and one respectively, each using only
propext, Classical.choice and Quot.sound. All logs and successful output
hashes matched the records at review time. The integrated rerun is separate.

The derivative is that of the literal symbol (2 sin(t/2))^(2m), with the
factor 2 from the inner function canceled by the half-angle derivative.
The bound uses |2 sin(t/2)|<=t for t>=0 and |cos|<=1, then a convex-segment
mean-value estimate; it is not assumed. The m=0 derivative degeneracy does
not affect the actual wrapper, which requires m>=2.

The phase-preimage bridge proves the actual published mesh lies in the
uniform domain and algebraically turns F_n(y)=j*pi into the same implicit
equation. It uses the previously proved interval uniqueness to identify y
with the fixed Y, including j=n. It does not choose a new Y for each index.
The comparison theorem retains the exponential factor, both size estimates,
and the exact h^(2m)*j^(2m-1) scale. The constant B=2m*A^(2m) has the correct
power from the derivative estimate and the angle displacement; the final
max only enlarges the uniform constant.

The final existence wrapper selects Y once from the previously constructed
Taylor/vanishing data and retains the same derivative-defined coefficient
family and uniform radius before all orders. It discharges the fixed-Y
uniqueness interface with that constructed Y. No low-index eigenvalue bound,
all-index expansion, extension independence or trace conclusion is claimed.
Imported phase-window and Taylor constructions have their separately scoped
reviews; this review does not claim a fresh replay of those dependencies.

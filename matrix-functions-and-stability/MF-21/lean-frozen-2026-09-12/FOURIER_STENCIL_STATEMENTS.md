# Concrete Fourier stencil statements

Statement lock for MF21Restart/FourierStencil.lean, 20 September 2026.

These statements concern the unchanged coefficient definition in
MF21Restart/Definitions.lean: the normalized cosine Fourier integral of
(2 sin(θ/2))^(2m) on [-π,π]. They do not assume an abstract coefficient
recurrence, a spectral expansion, or any version of Target.

The primary obligations, in namespace MF21Restart, are:

    theorem symbol_eq_cosine_power (m : ℕ) (θ : ℝ) :
        symbol m θ = (2 - 2 * Real.cos θ) ^ m

    theorem fourierCoeff_succ (m : ℕ) (k : ℤ) :
        fourierCoeff (m + 1) k =
          2 * fourierCoeff m k - fourierCoeff m (k - 1) -
            fourierCoeff m (k + 1)

    theorem fourierCoeff_zero (k : ℤ) :
        fourierCoeff 0 k = if k = 0 then 1 else 0

    theorem fourierCoeff_support (m : ℕ) (k : ℤ)
        (hk : (m : ℤ) < |k|) :
        fourierCoeff m k = 0

The direct matrix corollary uses the existing Toeplitz definition:

    theorem toeplitz_entry_eq_zero_of_lt_abs {m n : ℕ} (i j : Fin n)
        (hij : (m : ℤ) < |(i.val : ℤ) - (j.val : ℤ)|) :
        toeplitz m n i j = 0

The optional finite Laurent generating identity has the exact target:

    theorem fourierCoeff_laurent_sum (m : ℕ) (z : ℂ) (hz : z ≠ 0) :
        (∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
          (fourierCoeff m k : ℂ) * z ^ k) =
        (2 - z - z⁻¹) ^ m

Here k is an integer and z^k is the integer power. The support interval is
inclusive at both ends. No sign change in the Fourier convention changes
this identity, since fourierCoeff_neg is already proved for the concrete
even symbol. The nonzero hypothesis is essential for the Laurent form.

The proof may reuse the scalar trigonometric and integral strategy from the
frozen legacy file only after proving the symbol identity above. It must
import neither the legacy file nor any legacy target, bulk estimate, or
arbitrary-array wrapper. Recurrence and bandwidth are useful analytic
ingredients; these results do not prove the MF-21 asymptotic target and do
not increase the count of completed original problems. Local compilation
and any eventual Comparator execution are separate evidence obligations.

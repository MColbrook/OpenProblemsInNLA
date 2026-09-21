# Exact root-of-unity parameters: statement first

Frozen manuscript (2) and (8), 20 September 2026. Define the exact real
angles before casting into the complex exponential:

    def rootOmega (m ell : ℕ) : ℂ :=
      Complex.exp (((2 * Real.pi * (ell : ℝ) / (m : ℝ) : ℝ) : ℂ) * Complex.I)

    def rootKappa (m ell : ℕ) : ℂ :=
      Complex.exp (((Real.pi * (ell : ℝ) / (m : ℝ) - Real.pi / 2 : ℝ) : ℂ) *
        Complex.I)

These are the manuscript's omega_ell and kappa_ell, with ell running from
1 to m-1. No natural-number division occurs in either angle. The total
definitions at m=0 are harmless; positive-real-part assertions require
the actual index hypotheses.

Prove, without a branch or phase assumption:

    theorem rootKappa_re_pos (m ell : ℕ)
        (hell : 1 ≤ ell) (hellm : ell < m) :
      0 < (rootKappa m ell).re

    theorem rootKappa_norm (m ell : ℕ) : ‖rootKappa m ell‖ = 1

    theorem rootKappa_ne_zero (m ell : ℕ) : rootKappa m ell ≠ 0

    theorem rootKappa_sq (m ell : ℕ) :
      rootKappa m ell ^ 2 = -rootOmega m ell

The square identity must be derived from the complex exponential and
its pi-shift identity, not assumed. Re(kappa)>0 follows from the strict
angle range (equivalently sin(pi*ell/m)>0); excluding ell=0 and ell=m
is necessary. The norm and square identities hold for all natural m,ell.

For the already defined `stableRootCurve`, prove the literal equation (2):

    theorem stableRootCurve_rootOmega_equation (m ell : ℕ) (theta : ℝ) :
      2 - stableRootCurve (rootKappa m ell) theta -
          (stableRootCurve (rootKappa m ell) theta)⁻¹ =
        rootOmega m ell * ((2 - 2 * Real.cos theta : ℝ) : ℂ)

Derive this from `stableRootCurve_equation`, the proved kappa-square
identity, and the exact half-angle relation 4*sin(theta/2)^2=2-2*cos(theta).
This algebraic identity is valid for every real theta and total parameter
pair; the strict inside-root statement is applied later only for the
published indices and 0<theta≤pi, using the proved positive real part.

No all-index distinctness, uniqueness-of-root criterion, phase construction,
argument branch, exponential decay estimate, determinant asymptotic, or
MF-21 Target is claimed here. The original manuscript and frozen shared
definitions are unchanged. The authoring agent runs no compiler; the
coordinator supplies serial local testing after StableRootSmooth passes.

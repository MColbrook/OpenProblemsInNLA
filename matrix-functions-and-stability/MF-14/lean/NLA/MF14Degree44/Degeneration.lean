import NLA.MF14Degree44.Definitions

/-!
Explicit symbolic polynomial certificate data for the border degeneration.
The five scalar expressions are copied as data from the published independent
symbolic certificate. No JSON verdict or determinant assertion is imported.
Their required polynomial identities are proposed separately in Challenge.
Mathematical certificate: Marcus Webb, The University of Manchester.
Formalization preparation: George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology; Codex assistance.
-/

noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.MF14Degree44

def syzygyCoefficient1 (alpha eta gamma s : ℂ) : ℂ :=
  6*alpha^8*s^6 + 3*alpha^7*gamma^2*s^6 - 6*alpha^6*eta*s^6 + 3*alpha^5*gamma^3*s^5 - 9*alpha^5*s^4 + 6*alpha^4*eta*gamma*s^5 + 8*alpha^4*gamma^2*s^4 + 8*alpha^3*eta*s^4 - 2*alpha^3*gamma^4*s^4 + 3*alpha^3*gamma*s^3 - 1*alpha^2*eta*gamma^2*s^4 - 7*alpha^2*gamma^3*s^3 + 4*alpha*eta^2*s^4 + 2*alpha*eta*gamma*s^3 - 4*alpha*gamma^2*s^2 + 2*eta*gamma^3*s^3 + 1*eta*s^2 - 1*gamma*s

def syzygyCoefficient2 (alpha eta gamma s : ℂ) : ℂ :=
  2*alpha^10*s^8 + 1*alpha^9*gamma^2*s^8 - 2*alpha^8*eta*s^8 - 2*alpha^8*gamma*s^7 - 4*alpha^7*s^6 + 4*alpha^6*eta*gamma*s^7 - 2*alpha^6*gamma^2*s^6 + 6*alpha^5*eta*s^6 - 6*alpha^5*gamma*s^5 + 3*alpha^4*eta*gamma^2*s^6 - 6*alpha^4*gamma^3*s^5 + 7*alpha^4*s^4 + 8*alpha^3*eta^2*s^6 + 6*alpha^3*eta*gamma*s^5 + 2*alpha^3*gamma^5*s^5 - 19*alpha^3*gamma^2*s^4 - 1*alpha^2*eta*gamma^3*s^5 - 6*alpha^2*eta*s^4 + 7*alpha^2*gamma^4*s^4 - 6*alpha*eta^2*gamma*s^5 + 4*alpha*eta*gamma^2*s^4 + 4*alpha*gamma^3*s^3 + 2*eta^2*s^4 - 2*eta*gamma^4*s^4 - 5*eta*gamma*s^3 + 1*gamma^2*s^2

def syzygyCoefficient3 (alpha eta gamma s : ℂ) : ℂ :=
  -8*alpha^6*s^6 - 4*alpha^5*gamma^2*s^6 - 10*alpha^4*eta*s^6 - 4*alpha^4*gamma*s^5 + 3*alpha^3*gamma^3*s^5 - 2*alpha^3*s^4 + 12*alpha^2*eta*gamma*s^5 + 9*alpha^2*gamma^2*s^4 - 6*alpha*eta*s^4 - 3*alpha*gamma*s^3 - 2*eta*gamma^2*s^4 - 1*s^2

def syzygyCoefficient4 (alpha eta gamma s : ℂ) : ℂ :=
  9*alpha^5*s^6 - 8*alpha^3*gamma*s^5 + 3*alpha^2*s^4 - 1*alpha*gamma^2*s^4 - 1*eta*s^4 + 2*gamma*s^3

def syzygyCoefficient5 (alpha eta gamma s : ℂ) : ℂ :=
  -4*alpha^9*s^6 - 2*alpha^8*gamma^2*s^6 + 4*alpha^7*eta*s^6 + 2*alpha^7*gamma*s^5 - 1*alpha^6*gamma^3*s^5 + 10*alpha^6*s^4 - 6*alpha^5*eta*gamma*s^5 + 3*alpha^5*gamma^2*s^4 - 6*alpha^4*eta*s^4 - 2*alpha^4*gamma^4*s^4 + 15*alpha^4*gamma*s^3 - 2*alpha^3*eta*gamma^2*s^4 - 5*alpha^3*gamma^3*s^3 - 3*alpha^3*s^2 - 6*alpha^2*eta^2*s^4 - 12*alpha^2*eta*gamma*s^3 + 3*alpha^2*gamma^2*s^2 + 2*alpha*eta*gamma^3*s^3 + 6*alpha*eta*s^2 + 3*alpha*gamma*s + 2*eta^2*gamma*s^3 - 2*eta*gamma^2*s^2 + 1

def syzygyCoefficients (alpha eta gamma s : ℂ) : Fin 5 → ℂ :=
  ![syzygyCoefficient1 alpha eta gamma s, syzygyCoefficient2 alpha eta gamma s,
    syzygyCoefficient3 alpha eta gamma s, syzygyCoefficient4 alpha eta gamma s,
    syzygyCoefficient5 alpha eta gamma s]

def syzygyBasis (alpha eta gamma s : ℂ) : Fin 5 → Poly :=
  let q := Q alpha
  let r := Rparam alpha eta gamma s
  ![X ^ 2 * r, q ^ 2, q * r, r ^ 2, X * r]

def degenerationE (alpha eta gamma s : ℂ) : Poly :=
  ∑ i : Fin 5, C (syzygyCoefficients alpha eta gamma s i) *
    syzygyBasis alpha eta gamma s i

/-- An algebraic helper inside productSpan, never an allowed circuit primitive. -/
def lowPart6 (p : Poly) : Poly :=
  ∑ i : Fin 7, C (p.coeff i.val) * X ^ i.val

def borderC (alpha eta gamma s : ℂ) : ℂ :=
  -1 - 3 * alpha * gamma * s +
  (-2 * alpha ^ 3 + 9 * alpha ^ 2 * gamma ^ 2 - 6 * alpha * eta - 2 * eta * gamma ^ 2) * s ^ 2 +
  (-4 * alpha ^ 4 * gamma + 3 * alpha ^ 3 * gamma ^ 3 + 12 * alpha ^ 2 * eta * gamma) * s ^ 3 +
  (-8 * alpha ^ 6 - 4 * alpha ^ 5 * gamma ^ 2 - 10 * alpha ^ 4 * eta) * s ^ 4

def borderD (alpha eta gamma s : ℂ) : ℂ :=
  2 * gamma + (3 * alpha ^ 2 - alpha * gamma ^ 2 - eta) * s -
    8 * alpha ^ 3 * gamma * s ^ 2 + 9 * alpha ^ 5 * s ^ 3

/-- Polynomial extension of the normalized high coefficients, including s=0. -/
def degenerationZ (alpha eta gamma s : ℂ) : Poly :=
  let c := borderC alpha eta gamma s
  let d := borderD alpha eta gamma s
  C (-(3 * alpha * c + d * (2 * gamma +
    (6 * alpha ^ 2 + 2 * eta + 2 * alpha * gamma ^ 2) * s +
    2 * alpha ^ 3 * gamma * s ^ 2))) * X ^ 11 +
  C (-(c + s * d * ((6 * alpha + gamma ^ 2) +
    6 * alpha ^ 2 * gamma * s + alpha ^ 4 * s ^ 2))) * X ^ 12 +
  C (-(s * d * (2 + 6 * alpha * gamma * s + 4 * alpha ^ 3 * s ^ 2))) * X ^ 13 +
  C (-(s ^ 2 * d * (2 * gamma + 6 * alpha ^ 2 * s))) * X ^ 14 +
  C (-(4 * alpha * s ^ 3 * d)) * X ^ 15 + C (-(s ^ 3 * d)) * X ^ 16

end NLA.MF14Degree44

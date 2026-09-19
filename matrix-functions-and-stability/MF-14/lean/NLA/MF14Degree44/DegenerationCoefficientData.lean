/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. The mathematical syzygy is Marcus Webb's.

Small coefficient formulas for a generic linear combination of the five
syzygy-basis polynomials. The five coefficients remain independent inputs here.
-/
import NLA.MF14Degree44.Degeneration

noncomputable section
open Polynomial
namespace NLA.MF14Degree44

def syzygyR5 (alpha gamma s : ℂ) : ℂ := 1 + alpha * gamma * s
def syzygyR6 (alpha gamma s : ℂ) : ℂ := gamma * s + alpha ^ 2 * s ^ 2

def syzygyLowPartFor (alpha eta gamma s : ℂ) (c : Fin 5 → ℂ) : Poly :=
  C (c 4 * eta) * X ^ 4 +
  C (c 0 * eta + c 4 * alpha) * X ^ 5 +
  C (c 0 * alpha + c 1 * alpha ^ 2 + c 2 * alpha * eta + c 3 * eta ^ 2 +
    c 4 * syzygyR5 alpha gamma s) * X ^ 6

def syzygyMiddle7For (alpha eta gamma s : ℂ) (c : Fin 5 → ℂ) : ℂ :=
  c 0 * syzygyR5 alpha gamma s + 2 * c 1 * alpha + c 2 * (alpha ^ 2 + eta) +
    2 * c 3 * eta * alpha + c 4 * syzygyR6 alpha gamma s

def syzygyMiddle8For (alpha eta gamma s : ℂ) (c : Fin 5 → ℂ) : ℂ :=
  c 0 * syzygyR6 alpha gamma s + c 1 +
  c 2 * (alpha * syzygyR5 alpha gamma s + alpha) +
  c 3 * (2 * eta * syzygyR5 alpha gamma s + alpha ^ 2) + c 4 * (2 * alpha * s ^ 2)

def syzygyMiddle9For (alpha eta gamma s : ℂ) (c : Fin 5 → ℂ) : ℂ :=
  c 0 * (2 * alpha * s ^ 2) +
  c 2 * (alpha * syzygyR6 alpha gamma s + syzygyR5 alpha gamma s) +
  c 3 * (2 * eta * syzygyR6 alpha gamma s + 2 * alpha * syzygyR5 alpha gamma s) +
    c 4 * s ^ 2

def syzygyMiddle10For (alpha eta gamma s : ℂ) (c : Fin 5 → ℂ) : ℂ :=
  c 0 * s ^ 2 + c 2 * (alpha * (2 * alpha * s ^ 2) + syzygyR6 alpha gamma s) +
  c 3 * (2 * eta * (2 * alpha * s ^ 2) + 2 * alpha * syzygyR6 alpha gamma s +
    (syzygyR5 alpha gamma s) ^ 2)

def syzygyHighPartFor (alpha eta gamma s : ℂ) (c : Fin 5 → ℂ) : Poly :=
  C (c 2 * (alpha * s ^ 2 + 2 * alpha * s ^ 2) +
    c 3 * (2 * eta * s ^ 2 + 2 * alpha * (2 * alpha * s ^ 2) +
      2 * syzygyR5 alpha gamma s * syzygyR6 alpha gamma s)) * X ^ 11 +
  C (c 2 * s ^ 2 + c 3 * (2 * alpha * s ^ 2 +
    2 * syzygyR5 alpha gamma s * (2 * alpha * s ^ 2) +
    (syzygyR6 alpha gamma s) ^ 2)) * X ^ 12 +
  C (c 3 * (2 * syzygyR5 alpha gamma s * s ^ 2 +
    2 * syzygyR6 alpha gamma s * (2 * alpha * s ^ 2))) * X ^ 13 +
  C (c 3 * (2 * syzygyR6 alpha gamma s * s ^ 2 + (2 * alpha * s ^ 2) ^ 2)) * X ^ 14 +
  C (2 * c 3 * (2 * alpha * s ^ 2) * s ^ 2) * X ^ 15 +
  C (c 3 * (s ^ 2) ^ 2) * X ^ 16

end NLA.MF14Degree44

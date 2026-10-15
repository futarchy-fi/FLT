/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.DifferenceNodeNormalEquiv
public import FLT.Mazur.WeierstrassDilatationTangentEquiv

/-!
# The complete terminal arithmetic node with its actual smoothing constant

The original divided cubic is identified with the whole constant-product
node. The constant is constructed from the original coefficients and retained.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (ha : IsUnit W.a₁)
  (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "F" => terminalInversePolynomial W r I hI hrI ha
local notation "H" => terminalProductCorrection b3 b4 b6 r F
local notation "hH" => terminalProductCorrection_mem b3 b4 b6 r F I h4 h6 hrI

/-- The actual smoothing parameter constructed from the original terminal coefficients. -/
def terminalSmoothing : R := DifferenceNode.smoothingConstant H b3 I hI hH

/-- The constructed terminal smoothing retains the arithmetic vanishing ideal. -/
theorem terminalSmoothing_mem : terminalSmoothing W b3 b4 b6 r I hI hrI ha h4 h6 ∈ I :=
  DifferenceNode.smoothingConstant_mem H b3 I hI hH

/-- The smoothing constant retains b6 and both explicit correction terms. -/
theorem terminalSmoothing_formula :
    terminalSmoothing W b3 b4 b6 r I hI hrI ha h4 h6 = b6 +
      (b4 - b3 * r.eval ((F).eval (DifferenceNode.criticalDifference H b3 I hI hH))) *
        (F).eval (DifferenceNode.criticalDifference H b3 I hI hH) +
          DifferenceNode.criticalSlope H b3 I hI hH ^ 2 := by
  unfold terminalSmoothing DifferenceNode.smoothingConstant
  rw [show Polynomial.eval (DifferenceNode.criticalDifference H b3 I hI hH) H =
    (H).eval₂ (RingHom.id R) (DifferenceNode.criticalDifference H b3 I hI hH) from rfl]
  rw [terminalProductCorrection_eval]
  rfl

variable (hr : r ^ 2 + C W.a₁ * r = C W.a₂ + C s * X)

/-- The full terminal arithmetic chart is the constructed constant-product node. -/
def terminalNodeEquiv : Coordinate W s b3 b4 b6 ≃ₐ[R]
    NodalFiber.Coordinate (terminalSmoothing W b3 b4 b6 r I hI hrI ha h4 h6) :=
  (terminalTangentEquiv W s b3 b4 b6 r I hI hrI ha hr).trans
    (DifferenceNode.normalEquiv H b3 I hI hH)

/-- The full node comparison with its tangent root constructed from the original cubic. -/
def canonicalTerminalNodeEquiv (hs : s ∈ I) (h2 : W.a₂ ∈ I) :
    Coordinate W s b3 b4 b6 ≃ₐ[R] NodalFiber.Coordinate
      (terminalSmoothing W b3 b4 b6 (terminalTangentRoot W s I hI ha hs h2) I hI
        (terminalTangentRoot_mem W s I hI ha hs h2) ha h4 h6) :=
  terminalNodeEquiv W s b3 b4 b6 (terminalTangentRoot W s I hI ha hs h2) I hI
    (terminalTangentRoot_mem W s I hI ha hs h2) ha h4 h6
    (terminalTangentRoot_equation W s I hI ha hs h2)

end FLT.Mazur.WeierstrassDilatation

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationTerminalNode

/-!
# Explicit full terminal node coordinates in the original divided cubic

The two smoothing-node coordinates retain both polynomial changes and the
critical translation. These formulas can be evaluated on the original boundaries.
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
local notation "K" => DifferenceNode.normalCorrection H b3 I hI hH
local notation "hK" => DifferenceNode.normalCorrection_mem H b3 I hI hH
local notation "a" => DifferenceNode.criticalSlope H b3 I hI hH
local notation "A" => Coordinate W s b3 b4 b6
local notation "f" => algebraMap R A
local notation "P" => terminalSmallTangent W s b3 b4 b6 r
local notation "Q" => terminalOppositeTangent W s b3 b4 b6 r
local notation "c" => terminalSmoothing W b3 b4 b6 r I hI hrI ha h4 h6

/-- The first full terminal node coordinate as a function of the original cubic. -/
def terminalNodeSmall : A :=
  NilpotentQuadraticDifference.smallFactor K I hI hK f (P - f a) (Q + f a)

/-- The opposite full terminal node coordinate as a function of the original cubic. -/
def terminalNodeOpposite : A :=
  NilpotentQuadraticDifference.oppositeFactor K I hI hK f (P - f a) (Q + f a)

variable (hr : r ^ 2 + C W.a₁ * r = C W.a₂ + C s * X)
local notation "e" => terminalNodeEquiv W s b3 b4 b6 r I hI hrI ha h4 h6 hr

/-- The inverse node equivalence sends p to the explicit original first factor. -/
theorem terminalNodeEquiv_symm_p :
    (e).symm (NodalFiber.p c) = terminalNodeSmall W s b3 b4 b6 r I hI hrI ha h4 h6 := by
  change terminalTangentBackward W s b3 b4 b6 r I hI hrI ha hr
    (DifferenceNode.normalBackward H b3 I hI hH
      (NodalFiber.p (DifferenceNode.smoothingConstant H b3 I hI hH))) = _
  rw [DifferenceNode.normalBackward_p, DifferenceNode.normalSmall,
    NilpotentQuadraticDifference.smallFactor_map]
  simp only [map_sub, map_add, AlgHom.commutes, terminalTangentBackward_p,
    terminalTangentBackward_q, terminalNodeSmall]

/-- The inverse node equivalence sends q to the explicit original opposite factor. -/
theorem terminalNodeEquiv_symm_q :
    (e).symm (NodalFiber.q c) = terminalNodeOpposite W s b3 b4 b6 r I hI hrI ha h4 h6 := by
  change terminalTangentBackward W s b3 b4 b6 r I hI hrI ha hr
    (DifferenceNode.normalBackward H b3 I hI hH
      (NodalFiber.q (DifferenceNode.smoothingConstant H b3 I hI hH))) = _
  rw [DifferenceNode.normalBackward_q, DifferenceNode.normalOpposite,
    NilpotentQuadraticDifference.oppositeFactor_map]
  simp only [map_sub, map_add, AlgHom.commutes, terminalTangentBackward_p,
    terminalTangentBackward_q, terminalNodeOpposite]

include hr in
/-- The explicit original terminal factors have the actual retained smoothing as product. -/
theorem terminalNodeFactors_product :
    terminalNodeSmall W s b3 b4 b6 r I hI hrI ha h4 h6 *
      terminalNodeOpposite W s b3 b4 b6 r I hI hrI ha h4 h6 = f c := by
  rw [← terminalNodeEquiv_symm_p W s b3 b4 b6 r I hI hrI ha h4 h6 hr,
    ← terminalNodeEquiv_symm_q W s b3 b4 b6 r I hI hrI ha h4 h6 hr,
    ← map_mul, NodalFiber.relation, AlgEquiv.commutes]

end FLT.Mazur.WeierstrassDilatation

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationTerminalNodeCoordinates

/-!
# Restricting the complete terminal node with its explicit coordinates

Every original algebra-valued chart map induces a node map. Both node
coordinates retain the critical translation and the quadratic correction.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (ha : IsUnit W.a₁)
  (h4 : b4 ∈ I) (h6 : b6 ∈ I)
  (hr : r ^ 2 + C W.a₁ * r = C W.a₂ + C s * X)
local notation "A" => Coordinate W s b3 b4 b6
local notation "c" => terminalSmoothing W b3 b4 b6 r I hI hrI ha h4 h6
local notation "e" => terminalNodeEquiv W s b3 b4 b6 r I hI hrI ha h4 h6 hr
variable {S : Type*} [CommRing S] [Algebra R S] (g : Coordinate W s b3 b4 b6 →ₐ[R] S)

/-- Restriction of the whole computed smoothing node along an original chart map. -/
def terminalNodeRestriction : NodalFiber.Coordinate c →ₐ[R] S := g.comp (e).symm.toAlgHom

/-- The node restriction recovers every original function, not just the coordinates. -/
theorem terminalNodeRestriction_comp :
    (terminalNodeRestriction W s b3 b4 b6 r I hI hrI ha h4 h6 hr g).comp (e).toAlgHom = g := by
  apply AlgHom.ext
  intro z
  exact congrArg g ((e).symm_apply_apply z)

/-- The first restricted node coordinate is the explicit original corrected factor. -/
theorem terminalNodeRestriction_p :
    terminalNodeRestriction W s b3 b4 b6 r I hI hrI ha h4 h6 hr g (NodalFiber.p c) =
      g (terminalNodeSmall W s b3 b4 b6 r I hI hrI ha h4 h6) := by
  change g ((e).symm (NodalFiber.p c)) = _
  rw [terminalNodeEquiv_symm_p]

/-- The second restricted node coordinate is the explicit original corrected factor. -/
theorem terminalNodeRestriction_q :
    terminalNodeRestriction W s b3 b4 b6 r I hI hrI ha h4 h6 hr g (NodalFiber.q c) =
      g (terminalNodeOpposite W s b3 b4 b6 r I hI hrI ha h4 h6) := by
  change g ((e).symm (NodalFiber.q c)) = _
  rw [terminalNodeEquiv_symm_q]

local notation "F" => terminalInversePolynomial W r I hI hrI ha
local notation "H" => terminalProductCorrection b3 b4 b6 r F
local notation "hH" => terminalProductCorrection_mem b3 b4 b6 r F I h4 h6 hrI
local notation "K" => DifferenceNode.normalCorrection H b3 I hI hH
local notation "hK" => DifferenceNode.normalCorrection_mem H b3 I hI hH
local notation "a" => DifferenceNode.criticalSlope H b3 I hI hH
local notation "f" => algebraMap R S
local notation "P" => g (terminalSmallTangent W s b3 b4 b6 r)
local notation "Q" => g (terminalOppositeTangent W s b3 b4 b6 r)

/-- Evaluation of the first factor keeps the exact constructed polynomial correction. -/
theorem terminalNodeSmall_map :
    g (terminalNodeSmall W s b3 b4 b6 r I hI hrI ha h4 h6) =
      NilpotentQuadraticDifference.smallFactor K I hI hK f (P - f a) (Q + f a) := by
  unfold terminalNodeSmall
  rw [NilpotentQuadraticDifference.smallFactor_map]
  simp only [map_sub, map_add, AlgHom.commutes]

/-- Evaluation of the opposite factor keeps the exact constructed polynomial correction. -/
theorem terminalNodeOpposite_map :
    g (terminalNodeOpposite W s b3 b4 b6 r I hI hrI ha h4 h6) =
      NilpotentQuadraticDifference.oppositeFactor K I hI hK f (P - f a) (Q + f a) := by
  unfold terminalNodeOpposite
  rw [NilpotentQuadraticDifference.oppositeFactor_map]
  simp only [map_sub, map_add, AlgHom.commutes]

include hr in
/-- Both restricted factors retain the actual smoothing parameter. -/
theorem terminalNodeRestriction_product :
    g (terminalNodeSmall W s b3 b4 b6 r I hI hrI ha h4 h6) *
      g (terminalNodeOpposite W s b3 b4 b6 r I hI hrI ha h4 h6) = f c := by
  rw [← map_mul, terminalNodeFactors_product W s b3 b4 b6 r I hI hrI ha h4 h6 hr,
    AlgHom.commutes]

end FLT.Mazur.WeierstrassDilatation

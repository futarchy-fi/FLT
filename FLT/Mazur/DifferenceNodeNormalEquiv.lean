/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.DifferenceNodeNormalEvaluation

/-!
# The full constant-product normal form with its constructed inverse

Every corrected product with nilpotent coefficients is the actual smoothing
node with the computed constant. Both composites fix all coordinate functions.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.DifferenceNode
variable {R : Type*} [CommRing R] (h : R[X]) (b : R)
  (I : Ideal R) (hI : IsNilpotent I) (hh : h ∈ I.map C)
local notation "K" => normalCorrection h b I hI hh
local notation "hK" => normalCorrection_mem h b I hI hh
local notation "a" => criticalSlope h b I hI hh
local notation "c" => smoothingConstant h b I hI hh
local notation "A" => Coordinate h b
local notation "N" => NodalFiber.Coordinate c
local notation "P" => NodalFiber.p c
local notation "Q" => NodalFiber.q c
local notation "D" => NilpotentQuadraticDifference.inverseDifference K I hI hK
  (algebraMap R N) P Q
local notation "g" => normalBackward h b I hI hh
local notation "d" => q h b + algebraMap R A a - (p h b - algebraMap R A a)

/-- The original corrected quotient evaluates on the whole constant-product node. -/
def normalForward : A →ₐ[R] N :=
  normalEvaluation h b I hI hh P Q (NodalFiber.relation c)

local notation "f" => normalForward h b I hI hh

/-- The backward map recovers the original centered difference everywhere. -/
theorem normalBackward_difference : g D = d := by
  rw [NilpotentQuadraticDifference.inverseDifference_map, normalBackward_p, normalBackward_q]
  exact NilpotentQuadraticDifference.inverseDifference_original K I hI hK
    (algebraMap R A) (p h b - algebraMap R A a) (q h b + algebraMap R A a)

/-- The composite fixes every constant-product node function. -/
theorem normalForward_backward : (f).comp g = AlgHom.id R N := by
  apply NodalFiber.hom_ext
  · change f (g P) = P
    rw [normalBackward_p]
    exact normalEvaluation_small ..
  · change f (g Q) = Q
    rw [normalBackward_q]
    exact normalEvaluation_opposite ..

/-- The other composite fixes every original corrected tangent function. -/
theorem normalBackward_forward : (g).comp f = AlgHom.id R A := by
  apply hom_ext
  · change g (normalEvaluation h b I hI hh P Q (NodalFiber.relation c) (p h b)) = p h b
    rw [normalEvaluation_p]
    simp only [map_add, map_sub, map_mul, AlgHom.commutes,
      Polynomial.algHom_eval₂_algebraMap, normalBackward_p, normalBackward_difference]
    simp only [normalSmall, NilpotentQuadraticDifference.smallFactor]
    ring
  · change g (normalEvaluation h b I hI hh P Q (NodalFiber.relation c) (q h b)) = q h b
    rw [normalEvaluation_q]
    simp only [map_add, map_sub, map_mul, AlgHom.commutes,
      Polynomial.algHom_eval₂_algebraMap, normalBackward_q, normalBackward_difference]
    simp only [normalOpposite, NilpotentQuadraticDifference.oppositeFactor]
    ring

/-- The full corrected node is isomorphic to its constructed constant-product smoothing. -/
def normalEquiv : A ≃ₐ[R] N :=
  AlgEquiv.ofAlgHom f g (normalForward_backward h b I hI hh) (normalBackward_forward h b I hI hh)

end FLT.Mazur.DifferenceNode

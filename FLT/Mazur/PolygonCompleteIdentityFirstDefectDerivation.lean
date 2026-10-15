/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstDefectProduct

/-!
# The original reduced action defect as a genuine derivation

The canonical coefficient defect kills all original residue scalars and is
linear over them. With the original reduced scaling defining the node-module
structure on the Laurent pair, it is a derivation. Its values are still full
Laurent pairs: descent into the node algebra has not been assumed.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "e" => parameter (R) 1
local notation "B" => ChartRing (e)
local notation "N" => ChartRing (0 : R)
local notation "P" => ((R)[T;T⁻¹] × (R)[T;T⁻¹])
local notation "D" => completeIdentityFirstDefectCoefficient K n h i

/-- The actual coefficient defect kills every original residue scalar. -/
theorem completeIdentityFirstDefectCoefficient_scalar (r : R) :
    (D) (algebraMap (R) (N) r) = 0 := by
  have hr : firstNodeReduction (R) (algebraMap (S) (B) (algebraMap (R) (S) r)) =
      algebraMap (R) (N) r := by
    rw [firstNodeReduction, ringMap_scalar]
    exact congrArg (algebraMap (R) (N)) ((reduction (R) 1).commutes r)
  rw [← hr, completeIdentityFirstDefectCoefficient_reduction,
    completeIdentityFirstActionNodeDefect_apply]
  simp only [AlgHom.commutes, AlgEquiv.commutes, sub_self, map_zero]

/-- The canonical original coefficient map is linear over the entire retained parameter ring. -/
theorem completeIdentityFirstDefectCoefficient_smul (r : R) (z : N) :
    (D) (r • z) = r • (D) z := by
  rw [Algebra.smul_def r z, completeIdentityFirstDefectCoefficient_mul,
    completeIdentityFirstDefectCoefficient_scalar, zero_mul, zero_add,
    AlgHom.commutes, Algebra.smul_def r ((D) z), mul_comm]

/-- The actual additive coefficient defect with its proved residue-ring linearity. -/
def completeIdentityFirstDefectLinear : (N) →ₗ[R] (P) where
  toFun := D
  map_add' := (D).map_add
  map_smul' := completeIdentityFirstDefectCoefficient_smul K n h i

/-- A bundled derivation into the Laurent pair with the unchanged reduced scaling action. -/
def completeIdentityFirstDefectDerivation :
    let _ := (completeIdentityFirstReducedScaling K).toRingHom.toAlgebra
    Derivation (R) (N) (P) := by
  let _ := (completeIdentityFirstReducedScaling K).toRingHom.toAlgebra
  refine { toLinearMap := completeIdentityFirstDefectLinear K n h i
           map_one_eq_zero' := ?_
           leibniz' := ?_ }
  · change (D) 1 = 0
    simpa only [map_one] using completeIdentityFirstDefectCoefficient_scalar K n h i 1
  · intro z w
    change (D) (z * w) =
      completeIdentityFirstReducedScaling K z * (D) w +
        completeIdentityFirstReducedScaling K w * (D) z
    rw [completeIdentityFirstDefectCoefficient_mul]
    ring

/-- The derivation retains the computed original coefficient on every reduced node function. -/
theorem completeIdentityFirstDefectDerivation_apply (z : N) :
    completeIdentityFirstDefectDerivation K n h i z = (D) z := rfl

end FLT.Mazur.PolygonInfinitesimalStages

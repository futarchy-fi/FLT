/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingBranchSeparation
public import FLT.Mazur.PolygonInfinitesimalStages
public import FLT.Mazur.LaurentUnitPoints

/-!
# Reconstructing a node map from the original coordinate subalgebra

For two prescribed Laurent units, only two explicit pairs need to belong
to the original node subalgebra. Their lifts automatically satisfy xy = e,
so they construct a unique full node endomorphism. No node-map witness is
part of the input, and the two full branch restrictions are retained.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentUnitPoints
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R] (m : ℕ)
local notation "S" => Ring R m
local notation "e" => parameter R m
local notation "B" => ChartRing (e)
local notation "L" => (S)[T;T⁻¹]

/-- Both original punctured branches together at any truncated stage. -/
def stageNodeBranchPair : (B) →ₐ[S] ((L) × (L)) :=
  (leftLaurentMap (e)).prod ((leftLaurentMap (e)).comp (branchSwapMap (e)))

/-- The branch pair detects every function by full-branch separation. -/
theorem stageNodeBranchPair_injective : Function.Injective (stageNodeBranchPair R m) := by
  intro z w he
  apply eq_of_both_laurent (e) z w (congrArg Prod.fst he)
  exact congrArg LaurentPolynomial.invert (congrArg Prod.snd he)

/-- The original node coordinate subalgebra in its two complete Laurent branches. -/
def stageNodeBranchSubalgebra : Subalgebra (S) ((L) × (L)) := (stageNodeBranchPair R m).range

/-- The original node is identified with this subalgebra, retaining the nilpotent layer. -/
def stageNodeBranchEquiv : (B) ≃ₐ[S] stageNodeBranchSubalgebra R m :=
  AlgEquiv.ofInjective (stageNodeBranchPair R m) (stageNodeBranchPair_injective R m)

/-- The required image of x, determined by the two desired unit coordinates. -/
def stageNodeBranchLeftImage (u v : (L)ˣ) : (L) × (L) :=
  (u.val, C (e) * v⁻¹.val)

/-- The required image of y, determined by the same original unit coordinates. -/
def stageNodeBranchRightImage (u v : (L)ˣ) : (L) × (L) :=
  (C (e) * u⁻¹.val, v.val)

/-- Both branch pairs satisfy the actual smoothing relation before lifting. -/
theorem stageNodeBranchImages_mul (u v : (L)ˣ) :
    stageNodeBranchLeftImage R m u v * stageNodeBranchRightImage R m u v =
      stageNodeBranchPair R m (algebraMap (S) (B) (e)) := by
  rw [AlgHom.commutes]
  apply Prod.ext
  · change u.val * (C (e) * u⁻¹.val) = C (e)
    rw [mul_left_comm, Units.mul_inv, mul_one]
  · change C (e) * v⁻¹.val * v.val = C (e)
    rw [mul_assoc, Units.inv_mul, mul_one]

variable (u v : ((Ring R m)[T;T⁻¹])ˣ)
  (hx : stageNodeBranchLeftImage R m u v ∈ stageNodeBranchSubalgebra R m)
  (hy : stageNodeBranchRightImage R m u v ∈ stageNodeBranchSubalgebra R m)

/-- Reconstruct an actual node map from two coordinate-subalgebra membership proofs. -/
def stageNodeBranchReconstruct : (B) →ₐ[S] (B) :=
  evaluate (e) ((stageNodeBranchEquiv R m).symm ⟨stageNodeBranchLeftImage R m u v, hx⟩)
    ((stageNodeBranchEquiv R m).symm ⟨stageNodeBranchRightImage R m u v, hy⟩) (by
      apply (stageNodeBranchPair_injective R m)
      rw [map_mul]
      change ((stageNodeBranchEquiv R m) ((stageNodeBranchEquiv R m).symm _)).val *
        ((stageNodeBranchEquiv R m) ((stageNodeBranchEquiv R m).symm _)).val = _
      rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
      exact stageNodeBranchImages_mul R m u v)

/-- Reconstruction keeps the entire prescribed first-coordinate pair. -/
theorem stageNodeBranchReconstruct_left :
    stageNodeBranchPair R m (stageNodeBranchReconstruct R m u v hx hy (leftCoordinate (e))) =
      stageNodeBranchLeftImage R m u v := by
  rw [stageNodeBranchReconstruct, evaluate_left]
  exact congrArg Subtype.val ((stageNodeBranchEquiv R m).apply_symm_apply _)

/-- Reconstruction keeps the entire prescribed second-coordinate pair. -/
theorem stageNodeBranchReconstruct_right :
    stageNodeBranchPair R m (stageNodeBranchReconstruct R m u v hx hy (rightCoordinate (e))) =
      stageNodeBranchRightImage R m u v := by
  rw [stageNodeBranchReconstruct, evaluate_right]
  exact congrArg Subtype.val ((stageNodeBranchEquiv R m).apply_symm_apply _)

/-- The constructed first punctured-branch map agrees on every original node function. -/
theorem stageNodeBranchReconstruct_leftLaurent :
    (leftLaurentMap (e)).comp (stageNodeBranchReconstruct R m u v hx hy) =
      (evalUnit u).comp (leftLaurentMap (e)) := by
  apply chartRing_hom_ext (e)
  · exact (congrArg Prod.fst (stageNodeBranchReconstruct_left R m u v hx hy)).trans
      (by simp only [AlgHom.comp_apply, leftLaurentMap_left, evalUnit_T, zpow_one]; rfl)
  · exact (congrArg Prod.fst (stageNodeBranchReconstruct_right R m u v hx hy)).trans
      (by simp only [AlgHom.comp_apply, leftLaurentMap_right, map_mul,
        evalUnit_C, evalUnit_T, zpow_neg_one]; rfl)

/-- The second punctured-branch map also retains every original function. -/
theorem stageNodeBranchReconstruct_rightLaurent :
    ((leftLaurentMap (e)).comp (branchSwapMap (e))).comp
        (stageNodeBranchReconstruct R m u v hx hy) =
      (evalUnit v).comp ((leftLaurentMap (e)).comp (branchSwapMap (e))) := by
  apply chartRing_hom_ext (e)
  · exact (congrArg Prod.snd (stageNodeBranchReconstruct_left R m u v hx hy)).trans
      (by simp only [AlgHom.comp_apply, branchSwapMap_left, leftLaurentMap_right,
        map_mul, evalUnit_C, evalUnit_T, zpow_neg_one]; rfl)
  · exact (congrArg Prod.snd (stageNodeBranchReconstruct_right R m u v hx hy)).trans
      (by simp only [AlgHom.comp_apply, branchSwapMap_right, leftLaurentMap_left,
        evalUnit_T, zpow_one]; rfl)

end FLT.Mazur.PolygonInfinitesimalStages

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeBranchPair
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
variable (R : Type) [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "B" => ChartRing (e)
local notation "L" => (S)[T;T⁻¹]

/-- The original node coordinate subalgebra in its two complete Laurent branches. -/
def firstNodeBranchSubalgebra : Subalgebra (S) ((L) × (L)) := (firstNodeBranchPair R).range

/-- The original node is identified with this subalgebra, retaining the nilpotent layer. -/
def firstNodeBranchEquiv : (B) ≃ₐ[S] firstNodeBranchSubalgebra R :=
  AlgEquiv.ofInjective (firstNodeBranchPair R) (firstNodeBranchPair_injective R)

/-- The required image of x, determined by the two desired unit coordinates. -/
def firstNodeBranchLeftImage (u v : (L)ˣ) : (L) × (L) :=
  (u.val, C (e) * v⁻¹.val)

/-- The required image of y, determined by the same original unit coordinates. -/
def firstNodeBranchRightImage (u v : (L)ˣ) : (L) × (L) :=
  (C (e) * u⁻¹.val, v.val)

/-- Both branch pairs satisfy the actual smoothing relation before lifting. -/
theorem firstNodeBranchImages_mul (u v : (L)ˣ) :
    firstNodeBranchLeftImage R u v * firstNodeBranchRightImage R u v =
      firstNodeBranchPair R (algebraMap (S) (B) (e)) := by
  rw [AlgHom.commutes]
  apply Prod.ext
  · change u.val * (C (e) * u⁻¹.val) = C (e)
    rw [mul_left_comm, Units.mul_inv, mul_one]
  · change C (e) * v⁻¹.val * v.val = C (e)
    rw [mul_assoc, Units.inv_mul, mul_one]

variable (u v : ((Ring R 1)[T;T⁻¹])ˣ)
  (hx : firstNodeBranchLeftImage R u v ∈ firstNodeBranchSubalgebra R)
  (hy : firstNodeBranchRightImage R u v ∈ firstNodeBranchSubalgebra R)

/-- Reconstruct an actual node map from two coordinate-subalgebra membership proofs. -/
def firstNodeBranchReconstruct : (B) →ₐ[S] (B) :=
  evaluate (e) ((firstNodeBranchEquiv R).symm ⟨firstNodeBranchLeftImage R u v, hx⟩)
    ((firstNodeBranchEquiv R).symm ⟨firstNodeBranchRightImage R u v, hy⟩) (by
      apply (firstNodeBranchPair_injective R)
      rw [map_mul]
      change ((firstNodeBranchEquiv R) ((firstNodeBranchEquiv R).symm _)).val *
        ((firstNodeBranchEquiv R) ((firstNodeBranchEquiv R).symm _)).val = _
      rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
      exact firstNodeBranchImages_mul R u v)

/-- Reconstruction keeps the entire prescribed first-coordinate pair. -/
theorem firstNodeBranchReconstruct_left :
    firstNodeBranchPair R (firstNodeBranchReconstruct R u v hx hy (leftCoordinate (e))) =
      firstNodeBranchLeftImage R u v := by
  rw [firstNodeBranchReconstruct, evaluate_left]
  exact congrArg Subtype.val ((firstNodeBranchEquiv R).apply_symm_apply _)

/-- Reconstruction keeps the entire prescribed second-coordinate pair. -/
theorem firstNodeBranchReconstruct_right :
    firstNodeBranchPair R (firstNodeBranchReconstruct R u v hx hy (rightCoordinate (e))) =
      firstNodeBranchRightImage R u v := by
  rw [firstNodeBranchReconstruct, evaluate_right]
  exact congrArg Subtype.val ((firstNodeBranchEquiv R).apply_symm_apply _)

/-- The constructed first punctured-branch map agrees on every original node function. -/
theorem firstNodeBranchReconstruct_leftLaurent :
    (leftLaurentMap (e)).comp (firstNodeBranchReconstruct R u v hx hy) =
      (evalUnit u).comp (leftLaurentMap (e)) := by
  apply chartRing_hom_ext (e)
  · exact (congrArg Prod.fst (firstNodeBranchReconstruct_left R u v hx hy)).trans
      (by simp only [AlgHom.comp_apply, leftLaurentMap_left, evalUnit_T, zpow_one]; rfl)
  · exact (congrArg Prod.fst (firstNodeBranchReconstruct_right R u v hx hy)).trans
      (by simp only [AlgHom.comp_apply, leftLaurentMap_right, map_mul,
        evalUnit_C, evalUnit_T, zpow_neg_one]; rfl)

/-- The second punctured-branch map also retains every original function. -/
theorem firstNodeBranchReconstruct_rightLaurent :
    ((leftLaurentMap (e)).comp (branchSwapMap (e))).comp
        (firstNodeBranchReconstruct R u v hx hy) =
      (evalUnit v).comp ((leftLaurentMap (e)).comp (branchSwapMap (e))) := by
  apply chartRing_hom_ext (e)
  · exact (congrArg Prod.snd (firstNodeBranchReconstruct_left R u v hx hy)).trans
      (by simp only [AlgHom.comp_apply, branchSwapMap_left, leftLaurentMap_right,
        map_mul, evalUnit_C, evalUnit_T, zpow_neg_one]; rfl)
  · exact (congrArg Prod.snd (firstNodeBranchReconstruct_right R u v hx hy)).trans
      (by simp only [AlgHom.comp_apply, branchSwapMap_right, leftLaurentMap_left,
        evalUnit_T, zpow_one]; rfl)

end FLT.Mazur.PolygonInfinitesimalStages

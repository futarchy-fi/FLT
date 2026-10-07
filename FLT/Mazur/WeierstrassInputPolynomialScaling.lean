/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassProductOverlap
public import FLT.Mazur.WeierstrassProjectiveAdditionChart

/-!
# Homogeneous polynomial addition across input-chart changes

On the concrete input overlap the normalized inputs differ by units. The
polynomial addition coordinates therefore differ by the square of the product
of those units, so invertibility of every output coordinate is preserved.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (j k j' k' : Fin 3)

/-- First input normalizing factor in the simultaneous overlap. -/
def productOverlapLeftScale : ProductOverlap W j k j' k' :=
  (Algebra.TensorProduct.includeLeft (R := R) (S := R)
    (A := Overlap W j j') (B := Overlap W k k')) (overlapInverse W j j')

/-- Second input normalizing factor in the simultaneous overlap. -/
def productOverlapRightScale : ProductOverlap W j k j' k' :=
  (Algebra.TensorProduct.includeRight (R := R)
    (A := Overlap W j j') (B := Overlap W k k')) (overlapInverse W k k')

/-- Normalizing the first input multiplies every coordinate by the same factor. -/
theorem productOverlapOther_left (i : Fin 3) :
    productOverlapOther W j k j' k' (chartProductLeft W j' k' (coord W j' i)) =
      productOverlapLeftScale W j k j' k' *
        productOverlapRestriction W j k j' k' (chartProductLeft W j k (coord W j i)) := by
  let l : Overlap W j j' →ₐ[R] ProductOverlap W j k j' k' :=
    Algebra.TensorProduct.includeLeft
  have h₂ : productOverlapRestriction W j k j' k'
      (chartProductLeft W j k (coord W j i)) = l (overlapCoord W j j' i) :=
    DFunLike.congr_fun (Algebra.TensorProduct.map_comp_includeLeft
      (overlapRestriction W j j') (overlapRestriction W k k')) (coord W j i)
  calc
    _ = l (transitionBase W j j' (coord W j' i)) :=
      DFunLike.congr_fun (Algebra.TensorProduct.map_comp_includeLeft
        (transitionBase W j j') (transitionBase W k k')) (coord W j' i)
    _ = productOverlapLeftScale W j k j' k' * l (overlapCoord W j j' i) := by
      rw [transitionBase_coord, map_mul]
      rfl
    _ = _ := by rw [h₂]

/-- Normalizing the second input multiplies every coordinate by its own common factor. -/
theorem productOverlapOther_right (i : Fin 3) :
    productOverlapOther W j k j' k' (chartProductRight W j' k' (coord W k' i)) =
      productOverlapRightScale W j k j' k' *
        productOverlapRestriction W j k j' k' (chartProductRight W j k (coord W k i)) := by
  let l : Overlap W k k' →ₐ[R] ProductOverlap W j k j' k' :=
    Algebra.TensorProduct.includeRight
  have h₂ : productOverlapRestriction W j k j' k'
      (chartProductRight W j k (coord W k i)) = l (overlapCoord W k k' i) :=
    DFunLike.congr_fun (Algebra.TensorProduct.map_comp_includeRight
      (overlapRestriction W j j') (overlapRestriction W k k')) (coord W k i)
  calc
    _ = l (transitionBase W k k' (coord W k' i)) :=
      DFunLike.congr_fun (Algebra.TensorProduct.map_comp_includeRight
        (transitionBase W j j') (transitionBase W k k')) (coord W k' i)
    _ = productOverlapRightScale W j k j' k' * l (overlapCoord W k k' i) := by
      rw [transitionBase_coord, map_mul]
      rfl
    _ = _ := by rw [h₂]

/-- The common factor of the homogeneous addition polynomials after input normalization. -/
def productOverlapAdditionScale : ProductOverlap W j k j' k' :=
  (productOverlapLeftScale W j k j' k' * productOverlapRightScale W j k j' k') ^ 2

/-- The polynomial output factor is a unit on the entire input overlap. -/
theorem productOverlapAdditionScale_isUnit : IsUnit (productOverlapAdditionScale W j k j' k') :=
  (((overlapInverse_isUnit W j j').map (Algebra.TensorProduct.includeLeft (R := R) (S := R)
    (A := Overlap W j j') (B := Overlap W k k'))).mul
    ((overlapInverse_isUnit W k k').map (Algebra.TensorProduct.includeRight (R := R)
    (A := Overlap W j j') (B := Overlap W k k')))).pow 2

/-- All addition coordinates transform with the same invertible homogeneous factor. -/
theorem productOverlap_addition_scaled (i : Fin 3) :
    productOverlapOther W j k j' k' (chartProductAdditionCoordinates W j' k' i) =
      productOverlapAdditionScale W j k j' k' *
        productOverlapRestriction W j k j' k' (chartProductAdditionCoordinates W j k i) := by
  have hl : (fun a => productOverlapOther W j k j' k'
      (chartProductLeft W j' k' (coord W j' a))) =
      productOverlapLeftScale W j k j' k' • (fun a => productOverlapRestriction W j k j' k'
        (chartProductLeft W j k (coord W j a))) :=
    funext (productOverlapOther_left W j k j' k')
  have hr : (fun a => productOverlapOther W j k j' k'
      (chartProductRight W j' k' (coord W k' a))) =
      productOverlapRightScale W j k j' k' • (fun a => productOverlapRestriction W j k j' k'
        (chartProductRight W j k (coord W k a))) :=
    funext (productOverlapOther_right W j k j' k')
  have h₁ := congrFun (chartProductAdditionCoordinates_map W j' k'
    (productOverlapOther W j k j' k')) i
  have h₂ := congrFun (chartProductAdditionCoordinates_map W j k
    (productOverlapRestriction W j k j' k')) i
  simp only [Function.comp_def] at h₁ h₂
  rw [hl, hr, WeierstrassCurve.Projective.addXYZ_smul] at h₁
  exact h₁.trans (congrArg (productOverlapAdditionScale W j k j' k' * ·) h₂.symm)

/-- An output coordinate is invertible in one input presentation exactly when it is in the other. -/
theorem productOverlap_addition_isUnit_iff (i : Fin 3) :
    IsUnit (productOverlapOther W j k j' k' (chartProductAdditionCoordinates W j' k' i)) ↔
      IsUnit (productOverlapRestriction W j k j' k'
        (chartProductAdditionCoordinates W j k i)) := by
  rw [productOverlap_addition_scaled]
  exact ⟨isUnit_of_mul_isUnit_right, (productOverlapAdditionScale_isUnit W j k j' k').mul⟩

end FLT.Mazur.WeierstrassIntegralChart

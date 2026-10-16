/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopNodeTangentLift

/-!
# Exact classification of the original top-layer node infinitesimal endomorphisms

The constructed lift and the extracted split-node derivation are inverse.
In particular, a split-node derivation with the required branch restriction
is sufficient to construct a genuine extension on the original smoothing.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R] (m : ℕ)
local notation "S" => Ring R (m + 1)
local notation "e" => parameter R (m + 1)
local notation "B" => ChartRing (e)
local notation "N" => ChartRing (0 : R)

/-- Extracting the reduced vector field of the constructed lift recovers the given derivation. -/
theorem topNodeTangentLift_derivation (d : Derivation R (N) (N)) :
    topNodeDifferenceDerivation R m (topNodeTangentLift R m d)
      (topNodeTangentLift_restriction R m d) = d := by
  apply chartRing_derivation_ext (0 : R)
  · rw [topNodeDifferenceDerivation, derivationOfCoordinates_left]
    have he := topNodeDifference_reduction_unique R m (topNodeTangentLift R m d)
      (topNodeTangentLift_restriction R m d) (leftCoordinate (e))
      (topNodeFunctionLift R m (d (leftCoordinate (0 : R)))) (by
        rw [topNodeTangentLift_left, add_sub_cancel_left]
        exact Algebra.smul_def ((e) ^ (m + 1))
          (topNodeFunctionLift R m (d (leftCoordinate (0 : R)))))
    exact he.symm.trans (topNodeFunctionLift_reduction R m _)
  · rw [topNodeDifferenceDerivation, derivationOfCoordinates_right]
    have he := topNodeDifference_reduction_unique R m (topNodeTangentLift R m d)
      (topNodeTangentLift_restriction R m d) (rightCoordinate (e))
      (topNodeFunctionLift R m (d (rightCoordinate (0 : R)))) (by
        rw [topNodeTangentLift_right, add_sub_cancel_left]
        exact Algebra.smul_def ((e) ^ (m + 1))
          (topNodeFunctionLift R m (d (rightCoordinate (0 : R)))))
    exact he.symm.trans (topNodeFunctionLift_reduction R m _)

/-- Reconstructing an original endomorphism from its extracted derivation changes no coordinates. -/
theorem topNodeTangentLift_difference (f : (B) →ₐ[S] (B))
    (hf : ∀ z, topNodeRestriction R m (f z) = topNodeRestriction R m z) :
    topNodeTangentLift R m (topNodeDifferenceDerivation R m f hf) = f := by
  apply chartRing_hom_ext (e)
  · rw [topNodeTangentLift_left, topNodeDifferenceDerivation,
      derivationOfCoordinates_left]
    have he := topNodeFunctionLift_weighted R m
      (topNodeReduction R m (topNodeDifference R m f hf (leftCoordinate (e))))
      (topNodeDifference R m f hf (leftCoordinate (e))) rfl
    have hv := he.trans (topNodeDifference_spec R m f hf (leftCoordinate (e)))
    have hm := (Algebra.smul_def ((e) ^ (m + 1)) (topNodeFunctionLift R m
      (topNodeReduction R m (topNodeDifference R m f hf (leftCoordinate (e)))))).symm.trans hv
    rw [hm, add_sub_cancel]
  · rw [topNodeTangentLift_right, topNodeDifferenceDerivation,
      derivationOfCoordinates_right]
    have he := topNodeFunctionLift_weighted R m
      (topNodeReduction R m (topNodeDifference R m f hf (rightCoordinate (e))))
      (topNodeDifference R m f hf (rightCoordinate (e))) rfl
    have hv := he.trans (topNodeDifference_spec R m f hf (rightCoordinate (e)))
    have hm := (Algebra.smul_def ((e) ^ (m + 1)) (topNodeFunctionLift R m
      (topNodeReduction R m (topNodeDifference R m f hf (rightCoordinate (e)))))).symm.trans hv
    rw [hm, add_sub_cancel]

/-- Lifting constructs every original node endomorphism trivial at the preceding stage. -/
def topNodeTangentEquiv :
    Derivation R (N) (N) ≃
      {f : (B) →ₐ[S] (B) // ∀ z, topNodeRestriction R m (f z) = topNodeRestriction R m z} where
  toFun d := ⟨topNodeTangentLift R m d, topNodeTangentLift_restriction R m d⟩
  invFun f := topNodeDifferenceDerivation R m f.val f.property
  left_inv := topNodeTangentLift_derivation R m
  right_inv f := Subtype.ext (topNodeTangentLift_difference R m f.val f.property)

end FLT.Mazur.PolygonInfinitesimalStages

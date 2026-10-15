/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeTangentLift

/-!
# Exact classification of the original first-node infinitesimal endomorphisms

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
variable (R : Type) [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "B" => ChartRing (e)
local notation "N" => ChartRing (0 : R)

/-- Extracting the reduced vector field of the constructed lift recovers the given derivation. -/
theorem firstNodeTangentLift_derivation (d : Derivation R (N) (N)) :
    firstNodeDifferenceDerivation R (firstNodeTangentLift R d)
      (firstNodeTangentLift_reduction R d) = d := by
  apply chartRing_derivation_ext (0 : R)
  · rw [firstNodeDifferenceDerivation, derivationOfCoordinates_left]
    have he := firstNodeDifference_reduction_unique R (firstNodeTangentLift R d)
      (firstNodeTangentLift_reduction R d) (leftCoordinate (e))
      (firstNodeFunctionLift R (d (leftCoordinate (0 : R)))) (by
        rw [firstNodeTangentLift_left, add_sub_cancel_left]
        exact Algebra.smul_def (e) (firstNodeFunctionLift R (d (leftCoordinate (0 : R)))))
    exact he.symm.trans (firstNodeFunctionLift_reduction R _)
  · rw [firstNodeDifferenceDerivation, derivationOfCoordinates_right]
    have he := firstNodeDifference_reduction_unique R (firstNodeTangentLift R d)
      (firstNodeTangentLift_reduction R d) (rightCoordinate (e))
      (firstNodeFunctionLift R (d (rightCoordinate (0 : R)))) (by
        rw [firstNodeTangentLift_right, add_sub_cancel_left]
        exact Algebra.smul_def (e) (firstNodeFunctionLift R (d (rightCoordinate (0 : R)))))
    exact he.symm.trans (firstNodeFunctionLift_reduction R _)

/-- Reconstructing an original endomorphism from its extracted derivation changes no coordinates. -/
theorem firstNodeTangentLift_difference (f : (B) →ₐ[S] (B))
    (hf : ∀ z, firstNodeReduction R (f z) = firstNodeReduction R z) :
    firstNodeTangentLift R (firstNodeDifferenceDerivation R f hf) = f := by
  apply chartRing_hom_ext (e)
  · rw [firstNodeTangentLift_left, firstNodeDifferenceDerivation,
      derivationOfCoordinates_left]
    have he := firstNodeFunctionLift_weighted R
      (firstNodeReduction R (firstNodeDifference R f hf (leftCoordinate (e))))
      (firstNodeDifference R f hf (leftCoordinate (e))) rfl
    have hv := he.trans (firstNodeDifference_spec R f hf (leftCoordinate (e)))
    have hm := (Algebra.smul_def (e) (firstNodeFunctionLift R
      (firstNodeReduction R (firstNodeDifference R f hf (leftCoordinate (e)))))).symm.trans hv
    rw [hm, add_sub_cancel]
  · rw [firstNodeTangentLift_right, firstNodeDifferenceDerivation,
      derivationOfCoordinates_right]
    have he := firstNodeFunctionLift_weighted R
      (firstNodeReduction R (firstNodeDifference R f hf (rightCoordinate (e))))
      (firstNodeDifference R f hf (rightCoordinate (e))) rfl
    have hv := he.trans (firstNodeDifference_spec R f hf (rightCoordinate (e)))
    have hm := (Algebra.smul_def (e) (firstNodeFunctionLift R
      (firstNodeReduction R (firstNodeDifference R f hf (rightCoordinate (e)))))).symm.trans hv
    rw [hm, add_sub_cancel]

/-- All original first-node endomorphisms reducing to the identity are constructed by lifting. -/
def firstNodeTangentEquiv :
    Derivation R (N) (N) ≃
      {f : (B) →ₐ[S] (B) // ∀ z, firstNodeReduction R (f z) = firstNodeReduction R z} where
  toFun d := ⟨firstNodeTangentLift R d, firstNodeTangentLift_reduction R d⟩
  invFun f := firstNodeDifferenceDerivation R f.val f.property
  left_inv := firstNodeTangentLift_derivation R
  right_inv f := Subtype.ext (firstNodeTangentLift_difference R f.val f.property)

end FLT.Mazur.PolygonInfinitesimalStages

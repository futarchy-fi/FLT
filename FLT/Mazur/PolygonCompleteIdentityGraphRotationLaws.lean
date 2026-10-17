/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphRotation

/-!
# The cyclic action on the whole original graph

Rotation is invertible on both the original input and its full graph closure.
The action laws hold as morphisms, without reducing either scheme.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "H" => completeIdentityActionGraphClosure K n h
local notation "p" => completeIdentityActionGraphProjection K n h
local notation "l" => completeIdentityActionGraphLift K n h
local notation "r" => completeIdentityActionInputRotation K n h
local notation "R" => completeIdentityGraphRotation K n h

/-- Both original coordinates jointly detect equality on the full graph closure. -/
theorem completeIdentityGraph_hom_ext {T : Scheme} (f g : T ⟶ (H))
    (hs : f ≫ (p) = g ≫ (p)) (ht : f ≫ (l) = g ≫ (l)) : f = g := by
  apply (cancel_mono (completeIdentityActionGraphInclusion K n h)).mp
  apply pullback.hom_ext
  · exact hs
  · exact ht

/-- The zero rotation fixes the entire original input product. -/
theorem completeIdentityActionInputRotation_zero : r 0 = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [completeIdentityActionInputRotation_fst, Category.id_comp]
  · rw [completeIdentityActionInputRotation_snd, completeRotation_zero,
      Category.comp_id, Category.id_comp]

/-- Input rotation is an actual scheme isomorphism, including at singular points. -/
def completeIdentityActionInputRotationIso (b : ZMod n) :
    completeIdentityActionProduct K n h 0 ≅ completeIdentityActionProduct K n h 0 where
  hom := r b
  inv := r (-b)
  hom_inv_id := by rw [← completeIdentityActionInputRotation_add, add_neg_cancel,
    completeIdentityActionInputRotation_zero]
  inv_hom_id := by rw [← completeIdentityActionInputRotation_add, neg_add_cancel,
    completeIdentityActionInputRotation_zero]

instance completeIdentityActionInputRotation_isIso (b : ZMod n) : IsIso (r b) :=
  (completeIdentityActionInputRotationIso K n h b).isIso_hom

/-- The zero rotation fixes the unchanged complete graph. -/
theorem completeIdentityGraphRotation_zero : R 0 = 𝟙 _ := by
  apply completeIdentityGraph_hom_ext
  · rw [completeIdentityGraphRotation_source, completeIdentityActionInputRotation_zero,
      Category.comp_id, Category.id_comp]
  · rw [completeIdentityGraphRotation_target, completeRotation_zero,
      Category.comp_id, Category.id_comp]

/-- Graph rotations retain the original cyclic addition law. -/
theorem completeIdentityGraphRotation_add (b c : ZMod n) : R (b + c) = R b ≫ R c := by
  apply completeIdentityGraph_hom_ext
  · simp only [Category.assoc, completeIdentityGraphRotation_source,
      completeIdentityGraphRotation_source_assoc, completeIdentityActionInputRotation_add]
  · simp only [Category.assoc, completeIdentityGraphRotation_target,
      completeIdentityGraphRotation_target_assoc, completeRotation_add]

/-- The original whole graph carries an actual cyclic family of automorphisms. -/
def completeIdentityGraphRotationIso (b : ZMod n) : (H) ≅ (H) where
  hom := R b
  inv := R (-b)
  hom_inv_id := by rw [← completeIdentityGraphRotation_add, add_neg_cancel,
    completeIdentityGraphRotation_zero]
  inv_hom_id := by rw [← completeIdentityGraphRotation_add, neg_add_cancel,
    completeIdentityGraphRotation_zero]

instance completeIdentityGraphRotation_isIso (b : ZMod n) : IsIso (R b) :=
  (completeIdentityGraphRotationIso K n h b).isIso_hom

/-- The full graph action restricts to precisely the constructed smooth rotation. -/
@[reassoc] theorem completeIdentityGraphRotation_smooth (b : ZMod n) :
    completeIdentityActionSmoothToGraph K n h ≫ R b =
      completeIdentitySmoothGraphRotation K n h b := by
  apply completeIdentityGraph_hom_ext
  · rw [Category.assoc, completeIdentityGraphRotation_source,
      completeIdentityActionSmoothToGraph_projection_assoc,
      completeIdentitySmoothGraphRotation_source]
  · rw [Category.assoc, completeIdentityGraphRotation_target,
      completeIdentityActionSmoothToGraph_lift_assoc,
      completeIdentitySmoothGraphRotation_target]

end FLT.Mazur.PolygonInfinitesimalStages

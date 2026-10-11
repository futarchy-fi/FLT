/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingNormalizedOverlap

/-!
# The actual normalized boundary overlap commutes with coefficient change

Coefficient extension gives an actual cartesian square of the constructed
auxiliary overlaps. Its maps retain the original auxiliary point and the
boundary projection. The normalized slice morphism commutes with this map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type} [CommRing R] [CommRing S]
  (t : R) (h₂ : IsUnit (2 : R)) (ht : IsUnit t) (hf : IsUnit (1 + 432 * t))
  (a : R →+* S) (h₂' : IsUnit (2 : S)) (ht' : IsUnit (a t))
  (hf' : IsUnit (1 + 432 * a t))

/-- The original boundary coefficient points form the specified coefficient-change square. -/
theorem smoothParameter_spec_natural :
    Spec.map (CommRingCat.ofHom a) ≫
        Spec.map (CommRingCat.ofHom (smoothParameter t h₂ ht hf)) =
      Spec.map (CommRingCat.ofHom (smoothParameter (a t) h₂' ht' hf')) := by
  rw [← Spec.map_comp]
  exact congrArg (fun b => Spec.map (CommRingCat.ofHom b))
    (smoothParameter_natural t h₂ ht hf a h₂' ht' hf')

/-- The actual map between auxiliary overlaps induced by coefficient extension. -/
def smoothOverlapBaseChange :
    smoothAuxiliaryOverlap (a t) h₂' ht' hf' ⟶ smoothAuxiliaryOverlap t h₂ ht hf :=
  smoothAuxiliaryLift t h₂ ht hf (smoothAuxiliaryPoint (a t) h₂' ht' hf')
    (smoothAuxiliaryProjection (a t) h₂' ht' hf' ≫ Spec.map (CommRingCat.ofHom a)) (by
      rw [smoothAuxiliaryPoint_base, Category.assoc, smoothParameter_spec_natural])

/-- Coefficient extension retains the original full auxiliary point. -/
@[reassoc] theorem smoothOverlapBaseChange_point :
    smoothOverlapBaseChange t h₂ ht hf a h₂' ht' hf' ≫ smoothAuxiliaryPoint t h₂ ht hf =
      smoothAuxiliaryPoint (a t) h₂' ht' hf' :=
  smoothAuxiliaryLift_point _ _ _ _ _ _ _

/-- Coefficient extension retains the actual boundary coefficient square. -/
@[reassoc] theorem smoothOverlapBaseChange_projection :
    smoothOverlapBaseChange t h₂ ht hf a h₂' ht' hf' ≫ smoothAuxiliaryProjection t h₂ ht hf =
      smoothAuxiliaryProjection (a t) h₂' ht' hf' ≫ Spec.map (CommRingCat.ofHom a) :=
  smoothAuxiliaryLift_projection _ _ _ _ _ _ _

/-- The constructed auxiliary overlaps commute with the original coefficient base change. -/
theorem smoothOverlapBaseChange_isPullback :
    IsPullback (smoothOverlapBaseChange t h₂ ht hf a h₂' ht' hf')
      (smoothAuxiliaryProjection (a t) h₂' ht' hf') (smoothAuxiliaryProjection t h₂ ht hf)
      (Spec.map (CommRingCat.ofHom a)) := by
  apply IsPullback.of_right (h₁₂ := smoothAuxiliaryPoint t h₂ ht hf)
    (h₂₂ := Spec.map (CommRingCat.ofHom (smoothParameter t h₂ ht hf))) _
    (smoothOverlapBaseChange_projection t h₂ ht hf a h₂' ht' hf')
    (IsPullback.of_hasPullback _ _)
  rw [smoothOverlapBaseChange_point, smoothParameter_spec_natural]
  exact IsPullback.of_hasPullback _ _

/-- The actual morphism into the normalized slice commutes with coefficient extension. -/
@[reassoc] theorem smoothOverlapBaseChange_normalized :
    smoothOverlapBaseChange t h₂ ht hf a h₂' ht' hf' ≫ smoothNormalizedOverlap t h₂ ht hf =
      smoothNormalizedOverlap (a t) h₂' ht' hf' := by
  rw [smoothNormalizedOverlap, ← auxiliarySchemeNormalizedSlicePoint_natural,
    smoothOverlapBaseChange_point]
  rfl

end FLT.Mazur.OneGonSmoothing

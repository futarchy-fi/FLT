/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingAuxiliaryOverlap
public import FLT.Mazur.OneGonSmoothingNormalizedComparison
public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeNormalizationNaturality

/-!
# The actual boundary overlap maps to the normalized smooth atlas

Normalize the full auxiliary family on the constructed etale overlap.
Every affine test of this actual scheme retains its original boundary
coefficient map; the normalized family is therefore isomorphic to the
original boundary cubic on that test, preserving infinity and all labels.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open UniversalWeierstrass WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]
  (t : R) (h₂ : IsUnit (2 : R)) (ht : IsUnit t) (hf : IsUnit (1 + 432 * t))

/-- The actual morphism from the boundary overlap into the original normalized slice. -/
def smoothNormalizedOverlap : smoothAuxiliaryOverlap t h₂ ht hf ⟶ normalizedSlice :=
  auxiliarySchemeNormalizedSlicePoint (smoothAuxiliaryPoint t h₂ ht hf)

/-- The normalized slice map retains the entire original normalized auxiliary family. -/
@[reassoc] theorem smoothNormalizedOverlap_inclusion :
    smoothNormalizedOverlap t h₂ ht hf ≫ normalizedSliceInclusion =
      auxiliarySchemeNormalizedPoint (smoothAuxiliaryPoint t h₂ ht hf) :=
  auxiliarySchemeNormalizedSlicePoint_inclusion _

variable {S : Type} [CommRing S] (j : Spec (.of S) ⟶ smoothAuxiliaryOverlap t h₂ ht hf)

/-- The exact original boundary coefficient map on any affine test of the overlap. -/
def smoothOverlapCoefficient : R →+* S :=
  (Spec.preimage (j ≫ smoothAuxiliaryProjection t h₂ ht hf)).hom

/-- The recovered coefficient homomorphism retains the actual boundary projection. -/
theorem smoothOverlapCoefficient_spec :
    Spec.map (CommRingCat.ofHom (smoothOverlapCoefficient t h₂ ht hf j)) =
      j ≫ smoothAuxiliaryProjection t h₂ ht hf :=
  Spec.map_preimage _

include j in
/-- Two is a unit on every original affine overlap test. -/
theorem smoothOverlapTwo_isUnit : IsUnit (2 : S) := by
  simpa only [map_ofNat] using h₂.map (smoothOverlapCoefficient t h₂ ht hf j)

/-- The original boundary parameter stays invertible on every overlap test. -/
theorem smoothOverlapParameter_isUnit :
    IsUnit (smoothOverlapCoefficient t h₂ ht hf j t) :=
  ht.map (smoothOverlapCoefficient t h₂ ht hf j)

/-- The original complementary discriminant factor stays invertible on each overlap test. -/
theorem smoothOverlapFactor_isUnit :
    IsUnit (1 + 432 * smoothOverlapCoefficient t h₂ ht hf j t) := by
  simpa only [map_add, map_one, map_mul, map_ofNat] using
    hf.map (smoothOverlapCoefficient t h₂ ht hf j)

/-- Every actual affine overlap test retains the original boundary coefficient square. -/
theorem smoothOverlapPoint_base :
    (j ≫ smoothAuxiliaryPoint t h₂ ht hf) ≫ levelFour.hom =
      Spec.map (CommRingCat.ofHom
        (smoothParameter (smoothOverlapCoefficient t h₂ ht hf j t)
          (smoothOverlapTwo_isUnit t h₂ ht hf j)
          (smoothOverlapParameter_isUnit t h₂ ht hf j)
          (smoothOverlapFactor_isUnit t h₂ ht hf j))) := by
  rw [Category.assoc, smoothAuxiliaryPoint_base, ← Category.assoc,
    ← smoothOverlapCoefficient_spec]
  rw [← Spec.map_comp]
  exact congrArg (fun a => Spec.map (CommRingCat.ofHom a))
    (smoothParameter_natural t h₂ ht hf (smoothOverlapCoefficient t h₂ ht hf j) _ _ _)

/-- Restricting the global normalized overlap gives the original affine normalization. -/
theorem smoothNormalizedOverlap_affine :
    j ≫ smoothNormalizedOverlap t h₂ ht hf =
      auxiliaryFamilyNormalizedSlicePoint (j ≫ smoothAuxiliaryPoint t h₂ ht hf) := by
  rw [smoothNormalizedOverlap, ← auxiliarySchemeNormalizedSlicePoint_natural,
    auxiliarySchemeNormalizedSlicePoint_eq_affine]

/-- The actual normalized overlap family recovers the original boundary cubic on each test. -/
def smoothOverlapFamilyIso :
    integralCurve (auxiliaryPullbackEquation (auxiliaryPointSections
      (auxiliaryFamilyNormalizedPoint (j ≫ smoothAuxiliaryPoint t h₂ ht hf)))) ≅
        (family (smoothOverlapCoefficient t h₂ ht hf j t)).left :=
  smoothNormalizedIso _ (smoothOverlapTwo_isUnit t h₂ ht hf j)
    (smoothOverlapParameter_isUnit t h₂ ht hf j) (smoothOverlapFactor_isUnit t h₂ ht hf j)
    (j ≫ smoothAuxiliaryPoint t h₂ ht hf) (smoothOverlapPoint_base t h₂ ht hf j)

/-- The constructed overlap comparison keeps the original infinity section. -/
@[reassoc] theorem smoothOverlapFamilyIso_zero :
    integralCurveZero (auxiliaryPullbackEquation (auxiliaryPointSections
      (auxiliaryFamilyNormalizedPoint (j ≫ smoothAuxiliaryPoint t h₂ ht hf)))) ≫
        (smoothOverlapFamilyIso t h₂ ht hf j).hom =
          marking (smoothOverlapCoefficient t h₂ ht hf j t) :=
  smoothNormalizedIso_zero _ _ _ _ _ _

end FLT.Mazur.OneGonSmoothing

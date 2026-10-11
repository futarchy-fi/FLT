/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualitySmoothSpecialization

/-!
# Cartesian coefficient comparison for the original smooth cubic

The actual smooth coefficient map is a base change for every coefficient algebra.
This uses the full geometric smooth open, including bad reduction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open WeierstrassIntegralChart
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- Restricting the coefficient map to the actual smooth opens gives a Cartesian square. -/
theorem originalSmoothCoefficientMap_inclusion_isPullback :
    IsPullback (originalSmoothCoefficientMap S W)
      (integralSmoothOpen (W.map (algebraMap R S))).ι
      (integralSmoothOpen W).ι (integralCoefficientMorphism W) := by
  apply IsOpenImmersion.isPullback
  · exact (originalSmoothCoefficientMap_inclusion S W).symm
  · simpa only [Scheme.Opens.opensRange_ι] using
      integralCoefficientMorphism_preimage_smooth (S := S) W

/-- The original smooth coefficient morphism preserves the structure maps. -/
@[reassoc] theorem originalSmoothCoefficientMap_structure :
    originalSmoothCoefficientMap S W ≫ integralSmoothStructure W =
      integralSmoothStructure (W.map (algebraMap R S)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  change _ ≫ (integralSmoothOpen W).ι ≫ integralCurveStructure W = _
  rw [originalSmoothCoefficientMap_inclusion_assoc, integralCoefficientMorphism_structure]
  rfl

/-- The entire original smooth scheme commutes with arbitrary coefficient extension. -/
theorem originalSmoothCoefficientMap_isPullback :
    IsPullback (originalSmoothCoefficientMap S W)
      (integralSmoothStructure (W.map (algebraMap R S))) (integralSmoothStructure W)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (originalSmoothCoefficientMap_inclusion_isPullback S W).paste_vert
    (integralCoefficient_isPullback W)

/-- Canonical comparison with the base change of the original integral smooth scheme. -/
def originalSmoothCoefficientIso :
    (integralSmoothOpen (W.map (algebraMap R S))).toScheme ≅
      pullback (integralSmoothStructure W)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (originalSmoothCoefficientMap_isPullback S W).isoPullback

/-- The comparison retains the actual smooth coefficient map. -/
@[reassoc] theorem originalSmoothCoefficientIso_fst :
    (originalSmoothCoefficientIso S W).hom ≫ pullback.fst _ _ =
      originalSmoothCoefficientMap S W :=
  (originalSmoothCoefficientMap_isPullback S W).isoPullback_hom_fst

/-- The comparison retains the actual extended smooth structure map. -/
@[reassoc] theorem originalSmoothCoefficientIso_snd :
    (originalSmoothCoefficientIso S W).hom ≫ pullback.snd _ _ =
      integralSmoothStructure (W.map (algebraMap R S)) :=
  (originalSmoothCoefficientMap_isPullback S W).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth

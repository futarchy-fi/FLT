/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothCoefficientGroupIso

/-!
# Faithful descent detection for the original smooth coefficient comparison

A faithfully flat coefficient algebra detects equality of maps out of the
original smooth cubic. The detecting cover is the actual intrinsic extended
smooth cubic, so this applies to a nonsplit cubic after a splitting extension.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)
  (hS : (algebraMap R S).FaithfullyFlat)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))

include hS

/-- The actual smooth comparison is flat under a faithfully flat coefficient extension. -/
theorem originalSmoothCoefficientMap_flat_of_faithfullyFlat :
    Flat (originalSmoothCoefficientMap S W) := by
  let _ : Flat q := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap R S))).mpr hS |>.1
  exact MorphismProperty.of_isPullback (originalSmoothCoefficientMap_isPullback S W).flip
    (inferInstance : Flat q)

/-- Every original smooth point is covered by the intrinsic extended smooth scheme. -/
theorem originalSmoothCoefficientMap_surjective_of_faithfullyFlat :
    Surjective (originalSmoothCoefficientMap S W) := by
  let _ : Surjective q := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap R S))).mpr hS |>.2
  exact MorphismProperty.of_isPullback (originalSmoothCoefficientMap_isPullback S W).flip
    (inferInstance : Surjective q)

/-- The intrinsic smooth coefficient comparison detects equality of scheme morphisms. -/
theorem originalSmoothCoefficientMap_epi_of_faithfullyFlat :
    Epi (originalSmoothCoefficientMap S W) := by
  let _ := originalSmoothCoefficientMap_flat_of_faithfullyFlat S W hS
  let _ := originalSmoothCoefficientMap_surjective_of_faithfullyFlat S W hS
  exact Flat.epi_of_flat_of_surjective _

/-- Equality after an actual faithfully flat smooth coefficient comparison descends. -/
theorem originalSmoothCoefficientMap_hom_ext {Y : Scheme.{u}}
    (a b : (integralSmoothOpen W).toScheme ⟶ Y)
    (h : originalSmoothCoefficientMap S W ≫ a = originalSmoothCoefficientMap S W ≫ b) :
    a = b := by
  let _ := originalSmoothCoefficientMap_epi_of_faithfullyFlat S W hS
  exact (cancel_epi (originalSmoothCoefficientMap S W)).mp h

/-- Equality of original smooth-group endomorphisms can be checked after a splitting cover. -/
theorem originalSmoothGroup_endomorphism_ext
    (a b : integralSmoothGroup W ⟶ integralSmoothGroup W)
    (h : originalSmoothCoefficientMap S W ≫ a.hom.hom.hom.left =
      originalSmoothCoefficientMap S W ≫ b.hom.hom.hom.left) : a = b := by
  have he := originalSmoothCoefficientMap_hom_ext S W hS _ _ h
  apply CommGrp.hom_ext
  exact Over.OverMorphism.ext he

omit hS in
/-- A field extension, in particular a splitting field, detects original smooth morphisms. -/
theorem originalSmoothCoefficientMap_field_hom_ext
    {K L : Type u} [Field K] [Field L] [Algebra K L] (U : WeierstrassCurve K)
    {Y : Scheme.{u}} (a b : (integralSmoothOpen U).toScheme ⟶ Y)
    (h : originalSmoothCoefficientMap L U ≫ a = originalSmoothCoefficientMap L U ≫ b) :
    a = b :=
  originalSmoothCoefficientMap_hom_ext L U
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance) a b h

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSmoothFiniteFlatCartier
public import FLT.Mazur.BaseAdicQuotientSpectrum

/-!
# Cartier ideal sheaves from finite flat smooth coordinate quotients

The actual quotient spectrum identifies the closed family of a ring ideal.
This transfers its algebraic finite, flat and presentation properties to the
scheme criterion, retaining the full sheafified ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- Smooth curve coordinates with finite flat presented quotient give a Cartier ideal sheaf. -/
theorem effectiveCartier_baseIdeal_of_smooth_finite_flat
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R B]
    (I : Ideal B) [Module.Finite R (B ⧸ I)] [Module.Flat R (B ⧸ I)]
    [Algebra.FinitePresentation R (B ⧸ I)] :
    EffectiveCartier (BaseAdicThickening.baseIdeal (.of B) I) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let J := BaseAdicThickening.baseIdeal (.of B) I
  let e := BaseAdicThickening.quotientSpecIso (.of B) I
  have he : e.hom ≫ (J.subschemeι ≫ f) =
      Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I))) := by
    rw [← Category.assoc, BaseAdicThickening.quotientSpecIso_hom_ι, ← Spec.map_comp]
    rfl
  let _ : IsFinite (J.subschemeι ≫ f) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite e.hom, he]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  let _ : Flat (J.subschemeι ≫ f) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @Flat e.hom, he]
    exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let _ : LocallyOfFinitePresentation (J.subschemeι ≫ f) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @LocallyOfFinitePresentation e.hom, he]
    exact (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  let _ : SmoothOfRelativeDimension 1 f := by
    apply HasRingHomProperty.Spec_iff.mpr
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr inferInstance)
  exact effectiveCartier_of_affine_smooth_finite_flat f J

end FLT.Mazur.FCurve

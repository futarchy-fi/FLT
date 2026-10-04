/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ExactSourceDenominatorLift
public import FLT.Mazur.PrincipalAffineRefinement
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Spectra of exact-denominator refinements

The refined ring map gives a closed immersion when it is surjective, and its
composite with both target localizations is precisely the original map
restricted to the twice-localized source.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.RefinedChartSpectrum
open PrincipalAffineRefinement GeneratorDenominatorLocalization ExactSourceDenominatorLift
variable {K R Q : Type u} [CommRing K] [CommRing R] [CommRing Q]
  [Algebra K R] [Algebra K Q]
  (s : R) (f : Q →ₐ[K] Localization.Away s) (t : Q)
  (b : Localization.Away t)
  (hb : map f t b = algebraMap R (Localization.Away (f t)) s)

/-- The morphism between the actual twice-localized affine schemes. -/
def morphism : Spec (.of (Localization.Away (f t))) ⟶ Spec (.of (Localization.Away b)) :=
  Spec.map (CommRingCat.ofHom (refinedMap s (f t) (map f t) b hb).toRingHom)

/-- Surjectivity of the exact ring map proves closed immersion of its spectrum. -/
lemma isClosedImmersion (hsurj : Function.Surjective (refinedMap s (f t) (map f t) b hb)) :
    IsClosedImmersion (morphism s f t b hb) :=
  IsClosedImmersion.spec_of_surjective _ hsurj

/-- The spectrum commutes with both target inclusions and the source refinement. -/
@[reassoc]
lemma morphism_inclusions :
    morphism s f t b hb ≫ inclusion b ≫ inclusion t =
      inclusion (f t) ≫ Spec.map (CommRingCat.ofHom f.toRingHom) := by
  have he : (refinedMap s (f t) (map f t) b hb).toRingHom.comp
      ((algebraMap (Localization.Away t) (Localization.Away b)).comp
        (algebraMap Q (Localization.Away t))) =
      (algebraMap (Localization.Away s) (Localization.Away (f t))).comp f.toRingHom := by
    ext a
    exact (refinedMap_algebraMap s (f t) (map f t) b hb _).trans
      (map_algebraMap f t a)
  unfold morphism inclusion
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext he)

end FLT.Mazur.RefinedChartSpectrum

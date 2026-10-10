/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionRetainedProjStructuralMap

/-!
# Retained structural morphisms in original affine coefficients

The structural morphism is the spectrum map of the actual degree-zero
coefficient insertion, including the canonical global-sections comparison.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.SectionRetainedProjBaseCoefficients

open SectionGradedSum SectionRetainedProjStructuralMap

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} (L : X.Modules) [Fact (FCurve.LocallyFreeRankOne L)]
  (q : ℕ) [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)]
  {R : Type} [CommRing R] (f : X ⟶ Spec (.of R))

/-- Original affine coefficients placed in the unchanged degree-zero section ring. -/
def coefficients : R →+* RetainedSubringGrading.grade (grade L ⊤) q 0 :=
  (zeroScalars L q).comp (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)

/-- The retained structural morphism is induced by the actual affine coefficients. -/
theorem toBase_eq :
    toBase L q f = Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom (coefficients L q f)) := by
  have he : inv (Spec (.of R)).toSpecΓ = Spec.map (Scheme.ΓSpecIso (.of R)).inv := by
    apply (cancel_mono (Spec (.of R)).toSpecΓ).mp
    rw [IsIso.inv_hom_id, SpecMap_ΓSpecIso_inv_toSpecΓ]
  rw [toBase, toSpecFunctions, he]
  simp only [coefficients, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rfl

/-- Composition with a base coefficient map is ordinary composition of the same coefficients. -/
@[reassoc]
theorem toBase_specMap {S : Type} [CommRing S] (ρ : S →+* R) :
    toBase L q f ≫ Spec.map (CommRingCat.ofHom ρ) =
      Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom ((coefficients L q f).comp ρ)) := by
  rw [toBase_eq, Category.assoc, ← Spec.map_comp]
  rfl

end FLT.Mazur.SectionRetainedProjBaseCoefficients

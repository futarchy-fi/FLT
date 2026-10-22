/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientSectionRecovery
public import FLT.Mazur.CoefficientModelFiniteness

/-!+# Equality of original markings at a finite coefficient stage

Two sections agreeing after recovery agree at a finite enlargement.
Equality of the literal pulled-back sections follows, without assuming
that the original coefficient inclusion is faithfully flat.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.Approximation
open SectionCoverBaseChange
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Equality of two recovered sections is witnessed by finite coefficients. -/
theorem exists_coefficient_sections_eq {A : Type u} [CommRing A]
    (R : Subalgebra ℤ A) [Algebra.FiniteType ℤ R]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R)) [LocallyOfFiniteType q]
    (s t : Spec (.of R) ⟶ Y) (hs : s ≫ q = 𝟙 _) (ht : t ≫ q = 𝟙 _)
    (hst : Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ s =
      Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ t) :
    ∃ i : (CoefficientStage R)ᵒᵖ,
      (coefficientSpectrumToInitial R).app i ≫ s =
        (coefficientSpectrumToInitial R).app i ≫ t := by
  have (i : (CoefficientStage R)ᵒᵖ) :
      IsNoetherian ((coefficientSpectrumDiagram R).obj i) := by
    let _ := coefficientStage_isNoetherianRing i
    change IsNoetherian (Spec (.of i.unop.val))
    infer_instance
  let i₀ : (CoefficientStage R)ᵒᵖ := .op ⟨R, le_rfl, inferInstance⟩
  have he : (coefficientSpectrumToInitial R).app i₀ = 𝟙 _ := by
    change Spec.map (𝟙 _) = 𝟙 (Spec (.of R))
    exact Spec.map_id _
  obtain ⟨i, α, hi⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (coefficientSpectrumDiagram R) (coefficientSpectrumToInitial R) q
    (coefficientSpectrumCone R) (coefficientSpectrumIsLimit R)
    (i := i₀) s t (he.trans hs.symm) (he.trans ht.symm) hst
  exact ⟨i, hi⟩

/-- The actual section maps of the enlarged family agree at a finite stage. -/
theorem exists_coefficient_sectionMaps_eq {A : Type u} [CommRing A]
    (R : Subalgebra ℤ A) [Algebra.FiniteType ℤ R]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R)) [LocallyOfFiniteType q]
    (s t : Spec (.of R) ⟶ Y) (hs : s ≫ q = 𝟙 _) (ht : t ≫ q = 𝟙 _)
    (hst : Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ s =
      Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ t) :
    ∃ i : (CoefficientStage R)ᵒᵖ,
      sectionMap q ((coefficientSpectrumToInitial R).app i) s hs =
        sectionMap q ((coefficientSpectrumToInitial R).app i) t ht := by
  obtain ⟨i, hi⟩ := exists_coefficient_sections_eq R q s t hs ht hst
  refine ⟨i, ?_⟩
  apply pullback.hom_ext
  · simpa only [sectionMap_fst] using hi
  · simp only [sectionMap_snd]

end FLT.Mazur.Approximation

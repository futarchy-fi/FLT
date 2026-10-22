/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientSectionNeighborhood
public import FLT.Mazur.RelativeDimensionNeighborhood

/-!
# Relative dimension at a marking after finite coefficient enlargement

A smooth marking whose recovered smooth neighborhood has dimension d
acquires a dimension-d neighborhood at a finite stage. The refined family,
section, and their original Cartesian recovery maps are unchanged pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.Approximation
open SectionCoverBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A recovered dimension bound at a smooth marking descends to finite coefficients. -/
theorem exists_coefficient_dimension_marking {A : Type} [CommRing A]
    (R : Subalgebra ℤ A) [Algebra.FiniteType ℤ R]
    {X Y : Scheme} {r : X ⟶ Spec (.of A)} (p : Y ⟶ Spec (.of R))
    [LocallyOfFinitePresentation p] {a : X ⟶ Y}
    (h : IsPullback a r p (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
    (s : Spec (.of A) ⟶ X) (hs : s ≫ r = 𝟙 _)
    (t : Spec (.of R) ⟶ Y) (ht : t ≫ p = 𝟙 _)
    (he : Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ t = s ≫ a)
    (hts : t ⁻¹ᵁ p.smoothLocus = ⊤) (d : ℕ)
    [SmoothOfRelativeDimension d ((a ⁻¹ᵁ p.smoothLocus).ι ≫ r)] :
    ∃ (i : (CoefficientStage R)ᵒᵖ)
      (V : (pullback p ((coefficientSpectrumToInitial R).app i)).Opens),
      sectionMap p ((coefficientSpectrumToInitial R).app i) t ht ⁻¹ᵁ V = ⊤ ∧
      SmoothOfRelativeDimension d
        (V.ι ≫ pullback.snd p ((coefficientSpectrumToInitial R).app i)) ∧
      Spec.map (CommRingCat.ofHom i.unop.val.val.toRingHom) ≫
        sectionMap p ((coefficientSpectrumToInitial R).app i) t ht =
          s ≫ coefficientModelRecovery h i := by
  have hsm : (s ≫ a) ⁻¹ᵁ p.smoothLocus = ⊤ := by
    rw [← he, Scheme.Hom.comp_preimage, hts]
    simp
  obtain ⟨V, hV, hd⟩ := RelativeDimensionNeighborhood.exists_marking_open
    p r a h d s hsm
  obtain ⟨i, hi⟩ := exists_coefficient_section_neighborhood R p t ht V (he ▸ hV)
  let b := (coefficientSpectrumToInitial R).app i
  have hcart := (isPullback_morphismRestrict (pullback.fst p b) V).paste_vert
    (IsPullback.of_hasPullback p b)
  exact ⟨i, pullback.fst p b ⁻¹ᵁ V, hi,
    MorphismProperty.of_isPullback hcart hd, coefficientSection_recovery h s hs t ht he i⟩

end FLT.Mazur.Approximation

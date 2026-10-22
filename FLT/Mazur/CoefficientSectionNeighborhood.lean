/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientOpenNeighborhood
public import FLT.Mazur.CoefficientSectionRecovery

/-!
# Retaining a neighborhood of the original marking at finite coefficients

An open of the model containing the recovered marking contains the entire
model marking after finite enlargement. The refined open and section are
the literal pullbacks, so any smoothness already proved there persists.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.Approximation
open SectionCoverBaseChange
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Containment of the recovered marking in a fixed open descends to finite coefficients. -/
theorem exists_coefficient_section_neighborhood {A : Type u} [CommRing A]
    (R : Subalgebra ℤ A) [Algebra.FiniteType ℤ R]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R))
    (t : Spec (.of R) ⟶ Y) (ht : t ≫ p = 𝟙 _) (V : Y.Opens)
    (hV : (Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ t) ⁻¹ᵁ V = ⊤) :
    ∃ i : (CoefficientStage R)ᵒᵖ,
      sectionMap p ((coefficientSpectrumToInitial R).app i) t ht ⁻¹ᵁ
        (pullback.fst p ((coefficientSpectrumToInitial R).app i) ⁻¹ᵁ V) = ⊤ := by
  obtain ⟨i, hi⟩ := exists_coefficient_preimage_open_eq_top R (t ⁻¹ᵁ V)
    (by simpa only [Scheme.Hom.comp_preimage] using hV)
  refine ⟨i, ?_⟩
  rw [← Scheme.Hom.comp_preimage, sectionMap_fst, Scheme.Hom.comp_preimage]
  exact hi

/-- A section landing in a smooth open lands in the smooth locus of the whole family. -/
theorem section_smoothLocus_of_neighborhood {X S : Scheme.{u}}
    (p : X ⟶ S) [LocallyOfFinitePresentation p] (t : S ⟶ X)
    (V : X.Opens) [Smooth (V.ι ≫ p)] (ht : t ⁻¹ᵁ V = ⊤) :
    t ⁻¹ᵁ p.smoothLocus = ⊤ := by
  have hV : V ≤ p.smoothLocus := by
    intro x hx
    have he : V.ι ⁻¹ᵁ p.smoothLocus = ⊤ := by
      rw [Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.smoothLocus_eq_top]
    exact he.ge (show (⟨x, hx⟩ : V) ∈ (⊤ : V.toScheme.Opens) from trivial)
  exact top_unique (ht.ge.trans (Scheme.Hom.preimage_mono t hV))

end FLT.Mazur.Approximation

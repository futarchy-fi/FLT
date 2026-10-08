/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineFlatRefinement

/-!
# Affine faithfully flat refinements through a prescribed source chart

Adjoin a chosen affine source chart to a finite affine refinement. The
result stays affine and faithfully flat over the base, and contains the
chosen chart as an actual open summand. This retains points of the original
cover that need not lie in a previously chosen finite refinement.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeAffineDescent
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private lemma coprodDesc_property (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtSource P] {A B T : Scheme.{u}} (f : A ⟶ T) (g : B ⟶ T)
    (hf : P f) (hg : P g) : P (coprod.desc f g) := by
  apply IsZariskiLocalAtSource.of_openCover (P := P) (coprodOpenCover.{u, u} A B)
  intro i
  rcases i with i | i
  · simpa only [coprodOpenCover, coprod.inl_desc] using hf
  · simpa only [coprodOpenCover, coprod.inr_desc] using hg

variable {X Y W : Scheme.{u}} [IsAffine X] [IsAffine W]

/-- An affine refinement can retain a prescribed affine flat source as an open summand. -/
theorem exists_affine_fppf_refinement_through (p : Y ⟶ X)
    [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
    (v : W ⟶ Y) [Flat v] [LocallyOfFinitePresentation v] :
    ∃ (Z : Scheme.{u}) (_ : IsAffine Z) (b : Z ⟶ Y) (t : W ⟶ Z),
      Flat b ∧ LocallyOfFinitePresentation b ∧ Flat (b ≫ p) ∧ Surjective (b ≫ p) ∧
        IsOpenImmersion t ∧ t ≫ b = v := by
  obtain ⟨Z, hZ, b, hb, hfp, hg, hs⟩ := exists_affine_fppf_refinement p
  let := hZ
  let := hb
  let := hfp
  let := hg
  let := hs
  let c : Z ⨿ W ⟶ Y := coprod.desc b v
  have hc : Flat c := coprodDesc_property (@Flat) b v hb inferInstance
  have hcfp : LocallyOfFinitePresentation c :=
    coprodDesc_property (@LocallyOfFinitePresentation) b v hfp inferInstance
  have hsurj : Surjective (c ≫ p) := by
    have : Surjective ((coprod.inl : Z ⟶ Z ⨿ W) ≫ (c ≫ p)) := by
      simpa only [c, coprod.inl_desc_assoc] using hs
    exact Surjective.of_comp coprod.inl (c ≫ p)
  exact ⟨Z ⨿ W, inferInstance, c, coprod.inr, hc, hcfp, inferInstance, hsurj,
    inferInstance, coprod.inr_desc b v⟩

end FLT.Mazur.SchemeAffineDescent

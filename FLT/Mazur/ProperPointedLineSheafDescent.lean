/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientSectionDescent
public import FLT.Mazur.ProperLineSheafDescent

/-!
# Proper models retaining a section and an invertible sheaf

The finite coefficient model simultaneously preserves properness, finite
presentation, the given section, and the line sheaf. Both the section and
the sheaf recover along the same cartesian square.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Pointed proper families and their line sheaves have a common finite coefficient model. -/
theorem exists_proper_pointed_line_sheaf_descent {A : Type u} [CommRing A]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of A)) [IsProper p] [LocallyOfFinitePresentation p]
    (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (L : X.Modules) (hL : FLT.Mazur.FCurve.LocallyFreeRankOne L)
    (c : Set A) (hc : c.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ c ⊆ S ∧
      ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of S)) (M : Y.Modules),
        IsProper q ∧ LocallyOfFinitePresentation q ∧
        FLT.Mazur.FCurve.LocallyFreeRankOne M ∧
        ∃ (t : Spec (.of S) ⟶ Y) (f : X ⟶ Y),
          t ≫ q = 𝟙 _ ∧
          IsPullback f p q (Spec.map (CommRingCat.ofHom S.val.toRingHom)) ∧
          Spec.map (CommRingCat.ofHom S.val.toRingHom) ≫ t = s ≫ f ∧
          Nonempty ((Scheme.Modules.pullback f).obj M ≅ L) := by
  obtain ⟨S₀, hS₀, hc₀, Y, q, M, hq, hfp, hM, f, hf, ⟨e⟩⟩ :=
    exists_proper_finite_presentation_line_sheaf_descent p L hL c hc
  change IsPullback f p q (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)) at hf
  obtain ⟨i, t, ht, he⟩ := exists_coefficient_section hf s hs
  refine ⟨i.unop.val, i.unop.property.2, fun x hx ↦ i.unop.property.1 (hc₀ hx),
    (coefficientModelDiagram S₀ q).obj i,
    pullback.snd q ((coefficientSpectrumToInitial S₀).app i),
    coefficientModelSheaf (q := q) i M, inferInstance, inferInstance,
    coefficientModelSheaf_rankOne i hM, t, coefficientModelRecovery hf i, ht,
    coefficientModelRecovery_isPullback hf i, he, ?_⟩
  exact ⟨coefficientModelSheafRecoveryIso hf i e⟩

end FLT.Mazur.Approximation

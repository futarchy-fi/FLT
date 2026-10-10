/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientSmoothDescent
public import FLT.Mazur.ProperPointedLineSheafDescent

/-!
# Proper smooth pointed models with an invertible sheaf

Smoothness, properness, the section, and the line sheaf are retained at one
finite coefficient stage. The recovery square, section equation, and sheaf
isomorphism all use the same map from the original family.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Proper smooth pointed families with a line sheaf descend together to finite coefficients. -/
theorem exists_proper_smooth_pointed_line_sheaf_descent {A : Type u} [CommRing A]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of A)) [IsProper p] [Smooth p]
    (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (L : X.Modules) (hL : FLT.Mazur.FCurve.LocallyFreeRankOne L)
    (c : Set A) (hc : c.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ c ⊆ S ∧
      ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of S)) (M : Y.Modules),
        IsProper q ∧ Smooth q ∧ FLT.Mazur.FCurve.LocallyFreeRankOne M ∧
        ∃ (t : Spec (.of S) ⟶ Y) (f : X ⟶ Y),
          t ≫ q = 𝟙 _ ∧
          IsPullback f p q (Spec.map (CommRingCat.ofHom S.val.toRingHom)) ∧
          Spec.map (CommRingCat.ofHom S.val.toRingHom) ≫ t = s ≫ f ∧
          Nonempty ((Scheme.Modules.pullback f).obj M ≅ L) := by
  obtain ⟨S₀, hS₀, hc₀, Y, q, M, hq, hfp, hM, f, hf, ⟨e⟩⟩ :=
    exists_proper_finite_presentation_line_sheaf_descent p L hL c hc
  obtain ⟨i, _, hi⟩ := exists_coefficient_smooth_of_cartesian S₀ p q hf ∅ Set.finite_empty
  let qi := pullback.snd q ((coefficientSpectrumToInitial S₀).app i)
  let Mi := coefficientModelSheaf (q := q) i M
  have hMi : FLT.Mazur.FCurve.LocallyFreeRankOne Mi := coefficientModelSheaf_rankOne i hM
  have hfi := coefficientModelRecovery_isPullback hf i
  let ei := coefficientModelSheafRecoveryIso hf i e
  obtain ⟨j, t, ht, he⟩ := exists_coefficient_section hfi s hs
  refine ⟨j.unop.val, j.unop.property.2,
    fun x hx ↦ j.unop.property.1 (i.unop.property.1 (hc₀ hx)),
    (coefficientModelDiagram i.unop.val qi).obj j,
    pullback.snd qi ((coefficientSpectrumToInitial i.unop.val).app j),
    coefficientModelSheaf (q := qi) j Mi, inferInstance, inferInstance,
    coefficientModelSheaf_rankOne j hMi, t, coefficientModelRecovery hfi j,
    ht, coefficientModelRecovery_isPullback hfi j, he, ?_⟩
  exact ⟨coefficientModelSheafRecoveryIso hfi j ei⟩

end FLT.Mazur.Approximation

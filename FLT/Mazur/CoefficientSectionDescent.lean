/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientModelRecovery
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Descending a section to a finite coefficient enlargement

A section of the original family factors through a finite coefficient base
because the fixed model is locally finitely presented. The resulting section
of the enlarged model recovers the original section in its cartesian square.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A section descends to a finite coefficient stage, with its actual recovery identity. -/
theorem exists_coefficient_section {A : Type u} [CommRing A]
    {S₀ : Subalgebra ℤ A} [Algebra.FiniteType ℤ S₀]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {p : X ⟶ Spec (.of A)}
    {q : Y ⟶ Spec (.of S₀)} [LocallyOfFinitePresentation q]
    (h : IsPullback f p q (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)))
    (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    ∃ (i : (CoefficientStage S₀)ᵒᵖ)
      (t : (coefficientSpectrumDiagram S₀).obj i ⟶ (coefficientModelDiagram S₀ q).obj i),
      t ≫ pullback.snd q ((coefficientSpectrumToInitial S₀).app i) = 𝟙 _ ∧
      (coefficientSpectrumCone S₀).π.app i ≫ t = s ≫ coefficientModelRecovery h i := by
  have (i : (CoefficientStage S₀)ᵒᵖ) :
      IsAffine ((coefficientSpectrumDiagram S₀).obj i) := by
    change IsAffine (Spec (.of i.unop.val))
    infer_instance
  obtain ⟨i, a, ha, haq⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (coefficientSpectrumDiagram S₀) (coefficientSpectrumToInitial S₀) q
    (coefficientSpectrumCone S₀) (coefficientSpectrumIsLimit S₀) (s ≫ f) (by
      ext i
      change (coefficientSpectrumCone S₀).π.app i ≫
        (coefficientSpectrumToInitial S₀).app i = (s ≫ f) ≫ q
      rw [coefficientSpectrumCone_toInitial, Category.assoc, h.w, ← Category.assoc, hs]
      simp)
  refine ⟨i, pullback.lift a (𝟙 _) (by simpa using haq), by simp, ?_⟩
  apply pullback.hom_ext
  · simpa only [Category.assoc, pullback.lift_fst, coefficientModelRecovery_fst] using ha
  · simp only [coefficientModelRecovery, Category.assoc, pullback.lift_snd,
      Category.comp_id]
    rw [← Category.assoc, hs]
    exact (Category.id_comp _).symm

end FLT.Mazur.Approximation

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientModelLimit

/-!
# Simultaneous properties of finitely many fixed models

Properties that hold at individually chosen coefficient stages hold together
after one common enlargement. The models remain the base changes of the
original family, and any prescribed finite set of coefficients is retained.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

set_option backward.isDefEq.respectTransparency false

/-- Stable properties of finitely many fixed models hold at a common coefficient stage. -/
theorem exists_common_coefficient_properties {A : Type u} [CommRing A]
    (S₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ S₀]
    {ι : Type v} [Finite ι] {Y : ι → Scheme.{u}}
    (p : ∀ t, Y t ⟶ Spec (.of S₀))
    (W : ι → MorphismProperty Scheme.{u}) [∀ t, (W t).IsStableUnderBaseChange]
    (hW : ∀ t, ∃ i : (CoefficientStage S₀)ᵒᵖ,
      W t (pullback.snd (p t) ((coefficientSpectrumToInitial S₀).app i)))
    (c : Set A) (hc : c.Finite) :
    ∃ i : (CoefficientStage S₀)ᵒᵖ, c ⊆ i.unop.val ∧
      ∀ t, W t (pullback.snd (p t) ((coefficientSpectrumToInitial S₀).app i)) := by
  choose i hi using hW
  obtain ⟨S, hS, hcS, h₀S, hiS⟩ := exists_common_coefficient_extension S₀
    (fun t ↦ (i t).unop.val) (fun t ↦ (i t).unop.property.2) c hc
  let k : (CoefficientStage S₀)ᵒᵖ := .op ⟨S, h₀S, hS⟩
  refine ⟨k, hcS, fun t ↦ ?_⟩
  let α : k ⟶ i t := (homOfLE (show (i t).unop ≤ k.unop from hiS t)).op
  exact (W t).of_isPullback
    (schemeBaseChangeDiagram_isPullback (coefficientSpectrumToInitial S₀) (p t) α) (hi t)

end FLT.Mazur.Approximation

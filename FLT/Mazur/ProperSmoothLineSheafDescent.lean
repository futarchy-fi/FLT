/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientSmoothDescent
public import FLT.Mazur.ProperLineSheafDescent

/-!
# Proper smooth models of independently varying line bundles

Every line bundle on a proper smooth family over an arbitrary ring descends
with the family to finite integer coefficients. No section or preselected
model of the line bundle is required.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.Approximation
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Descend a proper smooth family and any line sheaf, retaining finite coefficients. -/
theorem exists_proper_smooth_line_sheaf_descent {A : Type u} [CommRing A]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of A)) [IsProper p] [Smooth p]
    (L : X.Modules) (hL : FCurve.LocallyFreeRankOne L) (c : Set A) (hc : c.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ c ⊆ S ∧
      ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of S)) (M : Y.Modules),
        IsProper q ∧ Smooth q ∧ FCurve.LocallyFreeRankOne M ∧
        ∃ a : X ⟶ Y,
          IsPullback a p q (Spec.map (CommRingCat.ofHom S.val.toRingHom)) ∧
          Nonempty ((Scheme.Modules.pullback a).obj M ≅ L) := by
  obtain ⟨S₀, hS₀, hc₀, Y, q, M, hq, hfp, hM, a, ha, ⟨e⟩⟩ :=
    exists_proper_finite_presentation_line_sheaf_descent p L hL c hc
  obtain ⟨i, _, hi⟩ := exists_coefficient_smooth_of_cartesian S₀ p q ha ∅ Set.finite_empty
  refine ⟨i.unop.val, i.unop.property.2, fun x hx ↦ i.unop.property.1 (hc₀ hx),
    (coefficientModelDiagram S₀ q).obj i,
    pullback.snd q ((coefficientSpectrumToInitial S₀).app i),
    coefficientModelSheaf (q := q) i M, inferInstance, hi,
    coefficientModelSheaf_rankOne i hM, coefficientModelRecovery ha i,
    coefficientModelRecovery_isPullback ha i, ?_⟩
  exact ⟨coefficientModelSheafRecoveryIso ha i e⟩

end FLT.Mazur.Approximation

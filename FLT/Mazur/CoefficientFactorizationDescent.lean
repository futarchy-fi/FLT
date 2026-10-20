/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientModelHomDescent

/-!
# Descending a factorization of a fixed coefficient model

A factorization after recovery descends after a finite coefficient enlargement.
The composite remains the original model map, rather than a newly chosen map
that merely agrees on points. The recovered factor is retained exactly.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A recovered factorization and its full composite equation descend together. -/
theorem exists_coefficient_factorization {A : Type u} [CommRing A]
    (S₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ S₀]
    {X Y Z : Scheme.{u}} (p : X ⟶ Spec (.of S₀))
    (q : Y ⟶ Spec (.of S₀)) (r : Z ⟶ Spec (.of S₀))
    [QuasiCompact p] [LocallyOfFiniteType p]
    [LocallyOfFinitePresentation q] [LocallyOfFiniteType r]
    (f : X ⟶ Z) (hf : f ≫ r = p) (j : Y ⟶ Z) (hj : j ≫ r = q)
    (a : (coefficientModelCone S₀ p).pt ⟶ Y)
    (ha : a ≫ q = pullback.fst p
      (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)) ≫ p)
    (haj : a ≫ j = pullback.fst p
      (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)) ≫ f) :
    ∃ (i : (CoefficientStage S₀)ᵒᵖ) (b : (coefficientModelDiagram S₀ p).obj i ⟶ Y),
      (coefficientModelCone S₀ p).π.app i ≫ b = a ∧
      b ≫ q = (coefficientModelToInitial S₀ p).app i ≫ p ∧
      b ≫ j = (coefficientModelToInitial S₀ p).app i ≫ f := by
  obtain ⟨i, b, hb, hbq⟩ := exists_coefficient_model_hom S₀ p q a ha
  obtain ⟨k, α, hk⟩ := exists_coefficient_model_hom_eq S₀ p r
    (b ≫ j) ((coefficientModelToInitial S₀ p).app i ≫ f)
    (by rw [Category.assoc, hj, hbq])
    (by rw [Category.assoc, hf]) (by
      rw [← Category.assoc, hb, haj, ← Category.assoc, coefficientModelCone_toInitial])
  refine ⟨k, (coefficientModelDiagram S₀ p).map α ≫ b, ?_, ?_, ?_⟩
  · rw [← Category.assoc, (coefficientModelCone S₀ p).w α, hb]
  · rw [Category.assoc, hbq, ← Category.assoc]
    exact congrArg (fun x => x ≫ p)
      ((coefficientModelToInitial S₀ p).naturality α)
  · rw [Category.assoc, hk, ← Category.assoc]
    exact congrArg (fun x => x ≫ f)
      ((coefficientModelToInitial S₀ p).naturality α)

end FLT.Mazur.Approximation

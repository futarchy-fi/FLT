/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientInverseEquations

/-!
# Invertibility descends for maps of finitely presented coefficient models

The descended inverse equations give an actual inverse to the base change
of the original map. No replacement map or injectivity of recovery is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A model morphism invertible after recovery becomes invertible at a finite stage. -/
theorem exists_coefficient_isIso {A : Type u} [CommRing A]
    (S₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ S₀]
    {Y Z : Scheme.{u}} (p : Y ⟶ Spec (.of S₀)) (q : Z ⟶ Spec (.of S₀))
    [QuasiCompact p] [QuasiCompact q]
    [LocallyOfFinitePresentation p] [LocallyOfFinitePresentation q]
    (f : Y ⟶ Z) (w : f ≫ q = p)
    [IsIso (immersionBaseChange p q f w
      (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)))] :
    ∃ i : (CoefficientStage S₀)ᵒᵖ,
      IsIso (immersionBaseChange p q f w ((coefficientSpectrumToInitial S₀).app i)) := by
  obtain ⟨i, a, ha, hleft, hright⟩ := exists_coefficient_inverse_equations S₀ p q f w
  let b := (coefficientSpectrumToInitial S₀).app i
  let g : pullback q b ⟶ pullback p b :=
    pullback.lift a (pullback.snd q b) (by
      change a ≫ p = pullback.snd q b ≫ b
      rw [ha]
      exact pullback.condition)
  refine ⟨i, ⟨⟨g, ?_, ?_⟩⟩⟩
  · apply pullback.hom_ext
    · simpa [g, b, Category.assoc, coefficientModelMorphism,
        coefficientModelToInitial] using hleft
    · simp [g, b, Category.assoc]
  · apply pullback.hom_ext
    · simpa [g, b, Category.assoc, coefficientModelToInitial] using hright
    · simp [g, b, Category.assoc]

end FLT.Mazur.Approximation

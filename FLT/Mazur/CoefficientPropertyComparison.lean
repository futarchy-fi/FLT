/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientIsomorphismDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Transferring properties between coefficient models

A fixed comparison map which becomes invertible after recovery becomes
invertible at a finite stage. Properties preserved by base change and
isomorphism can therefore be transferred to the original model at that stage.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [CommRing A] (S₀ : Subalgebra ℤ A)
  [Algebra.FiniteType ℤ S₀] {Y Z : Scheme.{u}}
  (p : Y ⟶ Spec (.of S₀)) (q : Z ⟶ Spec (.of S₀))
  [QuasiCompact p] [QuasiCompact q]
  [LocallyOfFinitePresentation p] [LocallyOfFinitePresentation q]
  (f : Y ⟶ Z) (w : f ≫ q = p)
  [IsIso (immersionBaseChange p q f w
    (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)))]

include f w in
/-- Properties invariant under base change and isomorphism transfer at a finite stage. -/
theorem exists_coefficient_property_of_comparison
    (W : MorphismProperty Scheme.{u}) [W.IsStableUnderBaseChange] [W.RespectsIso]
    (hq : W q) :
    ∃ i : (CoefficientStage S₀)ᵒᵖ,
      W (pullback.snd p ((coefficientSpectrumToInitial S₀).app i)) := by
  obtain ⟨i, hi⟩ := exists_coefficient_isIso S₀ p q f w
  let b := (coefficientSpectrumToInitial S₀).app i
  have hqi : W (pullback.snd q b) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback q b) hq
  refine ⟨i, ?_⟩
  rw [← immersionBaseChange_snd p q f w b]
  exact MorphismProperty.RespectsIso.precomp W _ _ hqi

include f w in
/-- Comparison with a smooth model makes the given model smooth after enlargement. -/
theorem exists_coefficient_smooth_of_comparison [Smooth q] :
    ∃ i : (CoefficientStage S₀)ᵒᵖ,
      Smooth (pullback.snd p ((coefficientSpectrumToInitial S₀).app i)) :=
  exists_coefficient_property_of_comparison S₀ p q f w @Smooth inferInstance

end FLT.Mazur.Approximation

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientModelHomDescent

/-!
# Descending maps with cartesian recovery

A morphism between the recovered families descends as a morphism between
their coefficient models over the same finite base. Its recovery square is
cartesian, as are the two family recovery squares.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- A morphism over the original ring descends with its actual cartesian recovery square. -/
theorem exists_coefficient_cartesian_hom {A : Type u} [CommRing A]
    (S₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ S₀]
    {Y Z : Scheme.{u}} (p : Y ⟶ Spec (.of S₀)) (q : Z ⟶ Spec (.of S₀))
    [QuasiCompact p] [LocallyOfFiniteType p] [LocallyOfFinitePresentation q]
    (F : (coefficientModelCone S₀ p).pt ⟶ (coefficientModelCone S₀ q).pt)
    (hF : F ≫ pullback.snd q (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)) =
      pullback.snd p (Spec.map (CommRingCat.ofHom S₀.val.toRingHom))) :
    ∃ (i : (CoefficientStage S₀)ᵒᵖ)
      (f : (coefficientModelDiagram S₀ p).obj i ⟶ (coefficientModelDiagram S₀ q).obj i),
      f ≫ pullback.snd q ((coefficientSpectrumToInitial S₀).app i) =
        pullback.snd p ((coefficientSpectrumToInitial S₀).app i) ∧
      IsPullback F ((coefficientModelCone S₀ p).π.app i)
        ((coefficientModelCone S₀ q).π.app i) f := by
  let b := Spec.map (CommRingCat.ofHom S₀.val.toRingHom)
  obtain ⟨i, a, ha, haq⟩ := exists_coefficient_model_hom S₀ p q
    (F ≫ pullback.fst q b) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hF, pullback.condition])
  let f : (coefficientModelDiagram S₀ p).obj i ⟶
      (coefficientModelDiagram S₀ q).obj i :=
    pullback.lift a (pullback.snd p ((coefficientSpectrumToInitial S₀).app i)) (by
      rw [haq]
      exact pullback.condition)
  have hf : f ≫ pullback.snd q ((coefficientSpectrumToInitial S₀).app i) =
      pullback.snd p ((coefficientSpectrumToInitial S₀).app i) := by simp [f]
  refine ⟨i, f, hf, ?_⟩
  apply IsPullback.of_right (h₁₂ := pullback.snd q b)
    (h₂₂ := pullback.snd q ((coefficientSpectrumToInitial S₀).app i))
    (v₁₃ := (coefficientSpectrumCone S₀).π.app i) ?_ ?_
    (coefficientModelCone_isPullback S₀ q i).flip
  · simpa only [b, hF, hf] using (coefficientModelCone_isPullback S₀ p i).flip
  · apply pullback.hom_ext
    · simpa [f, b, coefficientModelCone, schemeBaseChangeCone, Category.assoc] using ha.symm
    · simp only [f, coefficientModelCone, schemeBaseChangeCone, Category.assoc,
        pullback.map, pullback.lift_snd]
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun k ↦ k ≫ (coefficientSpectrumCone S₀).π.app i) hF)

end FLT.Mazur.Approximation

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientModelMorphism

/-!
# Descending both inverse equations to one coefficient stage

If a map of finitely presented models becomes invertible over the original
ring, its inverse descends, and both inverse equations hold at one common
coefficient enlargement.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- An inverse after recovery has both inverse equations at a common finite stage. -/
theorem exists_coefficient_inverse_equations {A : Type u} [CommRing A]
    (S₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ S₀]
    {Y Z : Scheme.{u}} (p : Y ⟶ Spec (.of S₀)) (q : Z ⟶ Spec (.of S₀))
    [QuasiCompact p] [QuasiCompact q]
    [LocallyOfFinitePresentation p] [LocallyOfFinitePresentation q]
    (f : Y ⟶ Z) (w : f ≫ q = p)
    [IsIso (immersionBaseChange p q f w
      (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)))] :
    ∃ (i : (CoefficientStage S₀)ᵒᵖ) (a : (coefficientModelDiagram S₀ q).obj i ⟶ Y),
      a ≫ p = (coefficientModelToInitial S₀ q).app i ≫ q ∧
      (coefficientModelMorphism S₀ p q f w).app i ≫ a =
        (coefficientModelToInitial S₀ p).app i ∧
      a ≫ f = (coefficientModelToInitial S₀ q).app i := by
  let b := Spec.map (CommRingCat.ofHom S₀.val.toRingHom)
  let F := coefficientModelMorphism S₀ p q f w
  let e := immersionBaseChange p q f w b
  let a₀ := inv e ≫ pullback.fst p b
  have ha₀ : a₀ ≫ p = pullback.fst q b ≫ q := by
    apply (cancel_epi e).mp
    simp [a₀, e, w, Category.assoc]
  obtain ⟨i, a, ha, hap⟩ := exists_coefficient_model_hom S₀ q p a₀ ha₀
  have hleft : (coefficientModelCone S₀ p).π.app i ≫ (F.app i ≫ a) =
      (coefficientModelCone S₀ p).π.app i ≫ (coefficientModelToInitial S₀ p).app i := by
    rw [← Category.assoc, coefficientModelMorphism_recovery, Category.assoc, ha]
    simp [a₀, e, b]
  have hright : (coefficientModelCone S₀ q).π.app i ≫ (a ≫ f) =
      (coefficientModelCone S₀ q).π.app i ≫ (coefficientModelToInitial S₀ q).app i := by
    rw [← Category.assoc, ha, coefficientModelCone_toInitial]
    apply (cancel_epi e).mp
    simp [a₀, e, b, Category.assoc]
  obtain ⟨j, α, hj⟩ := exists_coefficient_model_hom_eq S₀ p p
    (F.app i ≫ a) ((coefficientModelToInitial S₀ p).app i)
    (by rw [Category.assoc, hap, ← Category.assoc, coefficientModelMorphism_toInitial,
      Category.assoc, w]) rfl hleft
  obtain ⟨k, β, hk⟩ := exists_coefficient_model_hom_eq S₀ q q
    (a ≫ f) ((coefficientModelToInitial S₀ q).app i)
    (by rw [Category.assoc, w, hap]) rfl hright
  obtain ⟨l, γ, δ, he⟩ := IsCofiltered.cospan α β
  let τ := γ ≫ α
  refine ⟨l, (coefficientModelDiagram S₀ q).map τ ≫ a, ?_, ?_, ?_⟩
  · rw [Category.assoc, hap, ← Category.assoc]
    simp
  · rw [← Category.assoc, ← F.naturality, Category.assoc]
    change (coefficientModelDiagram S₀ p).map (γ ≫ α) ≫ (F.app i ≫ a) = _
    rw [Functor.map_comp, Category.assoc, hj, ← Category.assoc]
    simp
  · change ((coefficientModelDiagram S₀ q).map (γ ≫ α) ≫ a) ≫ f = _
    rw [he, Category.assoc, Functor.map_comp, Category.assoc, hk, ← Category.assoc]
    simp

end FLT.Mazur.Approximation

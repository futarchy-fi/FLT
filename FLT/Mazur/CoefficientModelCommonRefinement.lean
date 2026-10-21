/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientModelActualRecovery

/-!
# Independently descended maps agree at a common coefficient stage

The two maps may be chosen at different finite coefficient stages. Equality
on the original recovered scheme descends to a common finite enlargement,
retaining both transition maps and the original structure morphism.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.Approximation
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A : Type u} [CommRing A] (S₀ : Subalgebra ℤ A)
  [Algebra.FiniteType ℤ S₀] {Z Y : Scheme.{u}} (q : Z ⟶ Spec (.of S₀))
  [QuasiCompact q] [LocallyOfFiniteType q]
  (p : Y ⟶ Spec (.of S₀)) [LocallyOfFiniteType p]

/-- Independent finite-stage maps with the same recovery agree after common refinement. -/
theorem exists_coefficient_model_common_hom_eq
    {i j : (CoefficientStage S₀)ᵒᵖ}
    (a : (coefficientModelDiagram S₀ q).obj i ⟶ Y)
    (b : (coefficientModelDiagram S₀ q).obj j ⟶ Y)
    (ha : a ≫ p = (coefficientModelToInitial S₀ q).app i ≫ q)
    (hb : b ≫ p = (coefficientModelToInitial S₀ q).app j ≫ q)
    (hab : (coefficientModelCone S₀ q).π.app i ≫ a =
      (coefficientModelCone S₀ q).π.app j ≫ b) :
    ∃ (k : (CoefficientStage S₀)ᵒᵖ) (α : k ⟶ i) (β : k ⟶ j),
      (coefficientModelDiagram S₀ q).map α ≫ a =
        (coefficientModelDiagram S₀ q).map β ≫ b := by
  let l := IsCofiltered.min i j
  let α : l ⟶ i := IsCofiltered.minToLeft i j
  let β : l ⟶ j := IsCofiltered.minToRight i j
  let F := coefficientModelDiagram S₀ q
  have hα : (F.map α ≫ a) ≫ p = (coefficientModelToInitial S₀ q).app l ≫ q := by
    rw [Category.assoc, ha, ← Category.assoc]
    simp [F]
  have hβ : (F.map β ≫ b) ≫ p = (coefficientModelToInitial S₀ q).app l ≫ q := by
    rw [Category.assoc, hb, ← Category.assoc]
    simp [F]
  have he : (coefficientModelCone S₀ q).π.app l ≫ (F.map α ≫ a) =
      (coefficientModelCone S₀ q).π.app l ≫ (F.map β ≫ b) := by
    simpa only [F, ← Category.assoc, Cone.w] using hab
  obtain ⟨k, γ, hk⟩ := exists_coefficient_model_hom_eq S₀ q p
    (F.map α ≫ a) (F.map β ≫ b) hα hβ he
  refine ⟨k, γ ≫ α, γ ≫ β, ?_⟩
  simpa only [Functor.map_comp, Category.assoc] using hk

/-- The comparison applies to actual recovery projections from any specified original scheme. -/
theorem exists_coefficient_actual_common_hom_eq {X : Scheme.{u}}
    (e : X ≅ (coefficientModelCone S₀ q).pt)
    {i j : (CoefficientStage S₀)ᵒᵖ}
    (a : (coefficientModelDiagram S₀ q).obj i ⟶ Y)
    (b : (coefficientModelDiagram S₀ q).obj j ⟶ Y)
    (ha : a ≫ p = (coefficientModelToInitial S₀ q).app i ≫ q)
    (hb : b ≫ p = (coefficientModelToInitial S₀ q).app j ≫ q)
    (hab : coefficientActualRecovery S₀ q e i ≫ a =
      coefficientActualRecovery S₀ q e j ≫ b) :
    ∃ (k : (CoefficientStage S₀)ᵒᵖ) (α : k ⟶ i) (β : k ⟶ j),
      (coefficientModelDiagram S₀ q).map α ≫ a =
        (coefficientModelDiagram S₀ q).map β ≫ b := by
  apply exists_coefficient_model_common_hom_eq S₀ q p a b ha hb
  apply (cancel_epi e.hom).mp
  simpa only [coefficientActualRecovery, Category.assoc] using hab

end FLT.Mazur.Approximation

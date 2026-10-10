/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineChartBaseChange

/-!
# Further restriction of affine cross refinements

A commutative ring square with faithfully flat lower map refines both branches
of a cross refinement. Both independent covering maps are retained. Base change
provides such squares canonically using ring pushouts.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {C C' : Chart p} (ρ : C.CrossRefinement C')
variable {A B : CommRingCat.{u}} (ψ : A ⟶ B)
variable (α : ρ.baseRing ⟶ A) (β : ρ.coverRing ⟶ B)
variable (v : ρ.ringMap ≫ β = α ≫ ψ) (hψ : ψ.hom.FaithfullyFlat)

/-- Restrict both branches through the supplied geometric ring square. -/
def restrict : C.CrossRefinement C' where
  baseRing := A
  coverRing := B
  ringMap := ψ
  faithfullyFlat := hψ
  leftBase := ρ.leftBase ≫ α
  rightBase := ρ.rightBase ≫ α
  leftCover := ρ.leftCover ≫ β
  rightCover := ρ.rightCover ≫ β
  leftSquare := by
    rw [← Category.assoc, ρ.leftSquare, Category.assoc, v, Category.assoc]
  rightSquare := by
    rw [← Category.assoc, ρ.rightSquare, Category.assoc, v, Category.assoc]
  base_over := by rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    ρ.base_over]

/-- The first branch refines through the actual covering-ring map. -/
def restrictLeft : ρ.leftChart.Refinement (ρ.restrict ψ α β v hψ).leftChart where
  base := α
  cover := β
  square := v
  base_over := by simp only [leftChart, restrict, Spec.map_comp, Category.assoc]
  cover_over := by simp only [leftChart, restrict, Spec.map_comp, Category.assoc]

/-- The second branch retains its separate covering map through the same restriction. -/
def restrictRight : ρ.rightChart.Refinement (ρ.restrict ψ α β v hψ).rightChart where
  base := α
  cover := β
  square := v
  base_over := by simp only [rightChart, restrict, Spec.map_comp, Category.assoc]
  cover_over := by simp only [rightChart, restrict, Spec.map_comp, Category.assoc]

/-- The original first refinement followed by restriction is the new first refinement. -/
theorem leftRefinement_restrict :
    ρ.leftRefinement.comp (ρ.restrictLeft ψ α β v hψ) =
      (ρ.restrict ψ α β v hψ).leftRefinement := by
  ext <;> rfl

/-- The original second refinement followed by restriction is the new second refinement. -/
theorem rightRefinement_restrict :
    ρ.rightRefinement.comp (ρ.restrictRight ψ α β v hψ) =
      (ρ.restrict ψ α β v hψ).rightRefinement := by
  ext <;> rfl

/-- Any further affine base map has a constructed restriction of the common cover. -/
def baseChange : C.CrossRefinement C' :=
  ρ.restrict (pushout.inl α ρ.ringMap) α (pushout.inr α ρ.ringMap)
    pushout.condition.symm (ρ.leftChart.baseChange_faithfullyFlat α)

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement

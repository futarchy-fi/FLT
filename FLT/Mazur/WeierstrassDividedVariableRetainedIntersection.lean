/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPolygonAdjacencyClassification
public import FLT.Mazur.WeierstrassDividedPolygonRetainedIntersection
public import FLT.Mazur.PolygonVariableSmoothingIdentifiedIntersections

/-!
# Exact intersections of the two complete retained arms

Target equality forces either the identical original label or a consecutive
same-arm pair. In either orientation, the earlier point lies in its full
outgoing puncture.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (k : ℕ) (τ : R)
local notation "O" => fun (b : Bool) ↦
  ite (b = true) (Iso.hom (branchSwapIso R τ)) (𝟙 (PolygonSmoothing.chart R τ))

/-- Each possible full cyclic edge has the prescribed arm and outgoing puncture. -/
theorem variableRetained_classify (a d : Fin k) (b e : Bool)
    (x y : PolygonSmoothing.chart R τ)
    (h : (∃ z : branchTorus R,
      (finRotate (2 * k + 3)).symm (retainedPolygonIndex k a b) = retainedPolygonIndex k d e ∧
      leftBranchOpen R τ z = O b x ∧ precedingBranch R τ z = O e y) ∨
      (∃ z : branchTorus R,
      (finRotate (2 * k + 3)).symm (retainedPolygonIndex k d e) = retainedPolygonIndex k a b ∧
      precedingBranch R τ z = O b x ∧ leftBranchOpen R τ z = O e y)) :
    (a.val + 1 = d.val ∧ b = e ∧ x ∈ Set.range (leftBranchOpen R τ)) ∨
      (d.val + 1 = a.val ∧ b = e ∧ y ∈ Set.range (leftBranchOpen R τ)) := by
  rcases h with ⟨z, hz, hx, hy⟩ | ⟨z, hz, hx, hy⟩
  · rcases (retainedPolygonIndex_preceding_iff k a d b e).mp hz with
      ⟨rfl, rfl, ha⟩ | ⟨rfl, rfl, ha⟩
    · exact Or.inl ⟨ha, rfl, z, hx⟩
    · exact Or.inr ⟨ha, rfl, precedingBranch_swap_mem_left R τ y z hy⟩
  · rcases (retainedPolygonIndex_preceding_iff k d a e b).mp hz with
      ⟨rfl, rfl, ha⟩ | ⟨rfl, rfl, ha⟩
    · exact Or.inr ⟨ha, rfl, z, hy⟩
    · exact Or.inl ⟨ha, rfl, precedingBranch_swap_mem_left R τ x z hx⟩

variable (t : Fin (2 * k + 3) → R) [∀ i, Fact (IsNilpotent (t i))]
  (hr : ∀ a b, τ = t (retainedPolygonIndex k a b))
local notation "c" => PolygonVariableSmoothing.chartWithParameter R (2 * k + 3) t (by omega)
attribute [local irreducible] PolygonVariableSmoothing.chartWithParameter
  PolygonVariableSmoothing.scheme

/-- No additional intersections occur among the original retained labels. -/
theorem variableRetained_intersection (a d : Fin k) (b e : Bool)
    (x y : PolygonSmoothing.chart R τ)
    (h : c (retainedPolygonIndex k a b) τ (hr a b) (O b x) =
      c (retainedPolygonIndex k d e) τ (hr d e) (O e y)) :
    (a = d ∧ b = e) ∨
      (a.val + 1 = d.val ∧ b = e ∧ x ∈ Set.range (leftBranchOpen R τ)) ∨
      (d.val + 1 = a.val ∧ b = e ∧ y ∈ Set.range (leftBranchOpen R τ)) := by
  by_cases he : retainedPolygonIndex k a b = retainedPolygonIndex k d e
  · have hi := retainedPolygonIndex_injective k (a₁ := (a, b)) (a₂ := (d, e)) he
    exact Or.inl ⟨congrArg Prod.fst hi, congrArg Prod.snd hi⟩
  · exact Or.inr (variableRetained_classify R k τ a d b e x y
      ((PolygonVariableSmoothing.identifiedCharts_eq_iff R (2 * k + 3) t (by omega)
        he τ τ (hr a b) (hr d e) (O b x) (O e y)).mp h))

end FLT.Mazur.WeierstrassDividedDepth

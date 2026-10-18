/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPolygonAdjacencyClassification
public import FLT.Mazur.PolygonVariableSmoothingIdentifiedIntersections

/-!
# Initial and retained polygon intersections with their original orientation

An equality forces the first retained node on the same arm and the full
left puncture of the initial node. All other retained pairs are excluded.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonVariableSmoothing.chartWithParameter
  PolygonVariableSmoothing.scheme
variable (R : Type*) [CommRing R] (k : ℕ) (τ : R)
local notation "O" => fun (b : Bool) ↦
  ite (b = true) (Iso.hom (branchSwapIso R τ)) (𝟙 (PolygonSmoothing.chart R τ))

/-- Cyclic incidence on either arm locates the entire original initial puncture. -/
theorem variableInitial_classify (a : Fin k) (b d : Bool)
    (x y : PolygonSmoothing.chart R τ)
    (h : (∃ z : branchTorus R,
      (finRotate (2 * k + 3)).symm (initialPolygonIndex k b) = retainedPolygonIndex k a d ∧
      leftBranchOpen R τ z = O b x ∧ precedingBranch R τ z = y) ∨
      (∃ z : branchTorus R,
      (finRotate (2 * k + 3)).symm (retainedPolygonIndex k a d) = initialPolygonIndex k b ∧
      precedingBranch R τ z = O b x ∧ leftBranchOpen R τ z = y)) :
    a.val = 0 ∧ b = d ∧ x ∈ Set.range (leftBranchOpen R τ) := by
  rcases h with
    ⟨z, hz, hx, _⟩ | ⟨z, hz, hx, _⟩
  · obtain ⟨rfl, rfl, ha⟩ := (initialPolygonIndex_preceding_retained_iff k a b d).mp hz
    exact ⟨ha, rfl, z, hx⟩
  · obtain ⟨rfl, rfl, ha⟩ := (retainedPolygonIndex_preceding_initial_iff k a b d).mp hz
    refine ⟨ha, rfl, (edgeInversion R).hom z, ?_⟩
    have hp := congrArg (fun g ↦ g z) (precedingBranch_branchSwapIso R τ)
    have hs := congrArg (fun g ↦ g x) (branchSwapIso_involutive R τ)
    exact hp.symm.trans ((congrArg (branchSwapIso R τ).hom hx).trans hs)


variable (t : Fin (2 * k + 3) → R) [∀ i, Fact (IsNilpotent (t i))]
  (hi : ∀ b, τ = t (initialPolygonIndex k b))
  (hr : ∀ a b, τ = t (retainedPolygonIndex k a b))
local notation "c" => PolygonVariableSmoothing.chartWithParameter R (2 * k + 3) t (by omega)

/-- Every initial/retained equality locates the original first edge and its full puncture. -/
theorem variableInitial_retained_intersection (a : Fin k) (b d : Bool)
    (x y : PolygonSmoothing.chart R τ)
    (h : c (initialPolygonIndex k b) τ (hi b) (O b x) =
      c (retainedPolygonIndex k a d) τ (hr a d) y) :
    a.val = 0 ∧ b = d ∧ x ∈ Set.range (leftBranchOpen R τ) :=
  variableInitial_classify R k τ a b d x y
    ((PolygonVariableSmoothing.identifiedCharts_eq_iff R (2 * k + 3) t (by omega)
      (initialPolygonIndex_ne_retained k a b d) τ τ (hi b) (hr a d) (O b x) y).mp h)

end FLT.Mazur.WeierstrassDividedDepth

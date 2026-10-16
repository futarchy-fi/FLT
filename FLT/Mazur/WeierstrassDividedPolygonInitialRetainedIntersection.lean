/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPolygonAdjacencyClassification
public import FLT.Mazur.WeierstrassDividedRetainedPolygonMaps

/-!
# Initial and retained polygon intersections with their original orientation

An equality forces the first retained node on the same arm and the full
left puncture of the initial node. All other retained pairs are excluded.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing
variable (R : Type*) [CommRing R] (t : R) [Fact (IsNilpotent t)] (k : ℕ)
local notation "c" => PolygonInfinitesimal.chart R t (2 * k + 3) (by omega)
local notation "O" => fun (b : Bool) ↦
  ite (b = true) (Iso.hom (branchSwapIso R t)) (𝟙 (PolygonSmoothing.chart R t))

/-- Every initial/retained equality locates the original first edge and its full puncture. -/
theorem initialPolygon_retained_intersection (a : Fin k) (b d : Bool)
    (x y : PolygonSmoothing.chart R t)
    (h : (O b ≫ c (initialPolygonIndex k b)) x = c (retainedPolygonIndex k a d) y) :
    a.val = 0 ∧ b = d ∧ x ∈ Set.range (leftBranchOpen R t) := by
  rcases (PolygonInfinitesimal.charts_eq_iff R t (2 * k + 3) (by omega)
    (initialPolygonIndex_ne_retained k a b d) _ _).mp h with
    ⟨z, hz, hx, _⟩ | ⟨z, hz, hx, _⟩
  · obtain ⟨rfl, rfl, ha⟩ := (initialPolygonIndex_preceding_retained_iff k a b d).mp hz
    exact ⟨ha, rfl, z, hx⟩
  · obtain ⟨rfl, rfl, ha⟩ := (retainedPolygonIndex_preceding_initial_iff k a b d).mp hz
    refine ⟨ha, rfl, (edgeInversion R).hom z, ?_⟩
    have hp := congrArg (fun g ↦ g z) (precedingBranch_branchSwapIso R t)
    have hs := congrArg (fun g ↦ g x) (branchSwapIso_involutive R t)
    exact hp.symm.trans ((congrArg (branchSwapIso R t).hom hx).trans hs)

include k in
/-- Positive retention separates both initial nodes from the complete terminal chart. -/
theorem initialPolygon_terminal_disjoint (hk : 0 < k) (b : Bool) :
    Disjoint (Set.range (c (initialPolygonIndex k b))) (Set.range (c 0)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  rcases (PolygonInfinitesimal.charts_eq_iff R t (2 * k + 3) (by omega)
    (initialPolygonIndex_ne_terminal k b) x y).mp hy.symm with
    ⟨_, hz, _⟩ | ⟨_, hz, _⟩
  · exact initialPolygonIndex_preceding_ne_zero k hk b hz
  · exact zero_preceding_ne_initialPolygonIndex k hk b hz

end FLT.Mazur.WeierstrassDividedDepth

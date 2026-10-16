/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPolygonAdjacencyClassification
public import FLT.Mazur.WeierstrassDividedRetainedPolygonMaps

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
variable (R : Type*) [CommRing R] (t : R) [Fact (IsNilpotent t)] (k : ℕ)
local notation "c" => PolygonInfinitesimal.chart R t (2 * k + 3) (by omega)

omit [Fact (IsNilpotent t)] in
/-- Reversing an incoming point recovers the whole outgoing puncture. -/
theorem precedingBranch_swap_mem_left (x : PolygonSmoothing.chart R t)
    (z : branchTorus R) (h : precedingBranch R t z = (branchSwapIso R t).hom x) :
    x ∈ Set.range (leftBranchOpen R t) := by
  refine ⟨(edgeInversion R).hom z, ?_⟩
  have hp := congrArg (fun f ↦ f z) (precedingBranch_branchSwapIso R t)
  have hs := congrArg (fun f ↦ f x) (branchSwapIso_involutive R t)
  exact hp.symm.trans ((congrArg (branchSwapIso R t).hom h).trans hs)

/-- No additional intersections occur among the original retained labels. -/
theorem retainedPolygon_intersection (a d : Fin k) (b e : Bool)
    (x y : PolygonSmoothing.chart R t)
    (h : retainedPolygonMap R t k a b x = retainedPolygonMap R t k d e y) :
    (a = d ∧ b = e) ∨
      (a.val + 1 = d.val ∧ b = e ∧ x ∈ Set.range (leftBranchOpen R t)) ∨
      (d.val + 1 = a.val ∧ b = e ∧ y ∈ Set.range (leftBranchOpen R t)) := by
  by_cases he : retainedPolygonIndex k a b = retainedPolygonIndex k d e
  · have hi := retainedPolygonIndex_injective k (a₁ := (a, b)) (a₂ := (d, e)) he
    exact Or.inl ⟨congrArg Prod.fst hi, congrArg Prod.snd hi⟩
  change c (retainedPolygonIndex k a b) _ = c (retainedPolygonIndex k d e) _ at h
  rcases (PolygonInfinitesimal.charts_eq_iff R t (2 * k + 3) (by omega) he _ _).mp h with
    ⟨z, hz, hx, hy⟩ | ⟨z, hz, hx, hy⟩
  · rcases (retainedPolygonIndex_preceding_iff k a d b e).mp hz with
      ⟨rfl, rfl, ha⟩ | ⟨rfl, rfl, ha⟩
    · exact Or.inr (Or.inl ⟨ha, rfl, z, hx⟩)
    · exact Or.inr (Or.inr ⟨ha, rfl, precedingBranch_swap_mem_left R t y z hy⟩)
  · rcases (retainedPolygonIndex_preceding_iff k d a e b).mp hz with
      ⟨rfl, rfl, ha⟩ | ⟨rfl, rfl, ha⟩
    · exact Or.inr (Or.inr ⟨ha, rfl, z, hy⟩)
    · exact Or.inr (Or.inl ⟨ha, rfl, precedingBranch_swap_mem_left R t x z hx⟩)

end FLT.Mazur.WeierstrassDividedDepth

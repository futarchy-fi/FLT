/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPolygonInitialRetainedIntersection
public import FLT.Mazur.WeierstrassDividedPolygonLabelCover

/-!
# Separation of the complete infinity edge from the retained and terminal nodes

The edge lies in both initial charts. A retained intersection would have to
belong to both distinct Boolean arms, which the original labels exclude.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing
variable (R : Type*) [CommRing R] (t : R) [Fact (IsNilpotent t)] (k : ℕ)
local notation "c" => PolygonInfinitesimal.chart R t (2 * k + 3)
  (Nat.le_trans (Nat.le_succ 2) (Nat.le_add_left 3 (2 * k)))
local notation "e" => rightBranchOpen R t ≫ c (initialPolygonIndex k false)

/-- The whole common infinity edge is disjoint from every retained polygon node. -/
theorem initialPolygon_infinity_retained_disjoint (a : Fin k) (b : Bool) :
    Disjoint (Set.range e) (Set.range (c (retainedPolygonIndex k a b))) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  have hf := (initialPolygon_retained_intersection R t k a false b
    (rightBranchOpen R t x) y hy.symm).2.1
  have hx : e x ∈ Set.range (rightBranchOpen R t ≫
      (branchSwapIso R t).hom ≫ c (initialPolygonIndex k true)) := by
    rw [show Set.range (rightBranchOpen R t ≫ (branchSwapIso R t).hom ≫
      c (initialPolygonIndex k true)) = Set.range e from
        initialPolygon_infinity_edge_range R t k true]
    exact ⟨x, rfl⟩
  obtain ⟨z, hz⟩ := hx
  have ht := (initialPolygon_retained_intersection R t k a true b
    (rightBranchOpen R t z) y (hz.trans hy.symm)).2.1
  exact Bool.false_ne_true (hf.trans ht.symm)

/-- At positive depth the full infinity edge also avoids the complete terminal chart. -/
theorem initialPolygon_infinity_terminal_disjoint (hk : 0 < k) :
    Disjoint (Set.range e) (Set.range (c 0)) := by
  apply Disjoint.mono_left _ (initialPolygon_terminal_disjoint R t k hk false)
  rintro _ ⟨x, rfl⟩
  exact ⟨rightBranchOpen R t x, rfl⟩

end FLT.Mazur.WeierstrassDividedDepth

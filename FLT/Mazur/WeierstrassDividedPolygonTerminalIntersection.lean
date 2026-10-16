/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPolygonAdjacencyClassification
public import FLT.Mazur.WeierstrassDividedRetainedPolygonMaps

/-!
# Terminal adjacency keeps exactly the last original retained labels

Both cyclic orientations attach to zero only at their original last depth.
This excludes every earlier retained chart from the entire terminal image.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth

/-- On the descending arm, only the last retained node precedes zero. -/
theorem retainedPolygonIndex_preceding_zero_iff (k : ℕ) (a : Fin k) (b : Bool) :
    (finRotate (2 * k + 3)).symm (retainedPolygonIndex k a b) = 0 ↔
      b = false ∧ a.val + 1 = k := by
  rw [polygonPredecessor_eq_iff k _ _ (retainedPolygonIndex_ne_zero k a b)]
  cases b <;> simp [retainedPolygonIndex] <;> omega

/-- Across the cyclic boundary, zero precedes only the last opposite retained node. -/
theorem zero_preceding_retainedPolygonIndex_iff (k : ℕ) (a : Fin k) (b : Bool) :
    (finRotate (2 * k + 3)).symm 0 = retainedPolygonIndex k a b ↔
      b = true ∧ a.val + 1 = k := by
  have he : (finRotate (2 * k + 3)).symm 0 = ⟨2 * k + 2, by omega⟩ :=
    (Equiv.symm_apply_eq _).mpr finRotate_last'.symm
  rw [he, Fin.ext_iff]
  cases b <;> simp [retainedPolygonIndex] <;> omega

variable (R : Type*) [CommRing R] (t : R) [Fact (IsNilpotent t)] (k : ℕ)
local notation "c" => PolygonInfinitesimal.chart R t (2 * k + 3) (by omega)

/-- A full retained/terminal equality forces the original last retained depth. -/
theorem retainedPolygon_terminal_location (a : Fin k) (b : Bool)
    (x y : PolygonSmoothing.chart R t)
    (h : c (retainedPolygonIndex k a b) x = c 0 y) : a.val + 1 = k := by
  rcases (PolygonInfinitesimal.charts_eq_iff R t (2 * k + 3) (by omega)
    (retainedPolygonIndex_ne_zero k a b) x y).mp h with
    ⟨_, hz, _⟩ | ⟨_, hz, _⟩
  · exact ((retainedPolygonIndex_preceding_zero_iff k a b).mp hz).2
  · exact ((zero_preceding_retainedPolygonIndex_iff k a b).mp hz).2

end FLT.Mazur.WeierstrassDividedDepth

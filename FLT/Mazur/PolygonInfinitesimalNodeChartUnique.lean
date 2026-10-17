/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalAtlas
public import FLT.Mazur.PolygonSmoothingCoordinateIdeal

/-!
# An original node has a unique cyclic chart label

The explicit two-coordinate node locus misses all chart overlaps, including
both overlaps of the two-gon. This works over arbitrary nilpotent coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimal
open PolygonSmoothing
variable (R : Type*) [CommRing R] (t : R) [Fact (IsNilpotent t)]
  (n : ℕ) (h : 2 ≤ n)

/-- A point containing the original node ideal cannot belong to two different node charts. -/
theorem node_chart_label_unique {i j : Fin n} (x y : PolygonSmoothing.chart R t)
    (hx : coordinateIdeal t ≤ x.asIdeal)
    (he : chart R t n h i x = chart R t n h j y) : i = j := by
  by_contra hn
  have hl : leftCoordinate t ∈ x.asIdeal := hx (Ideal.subset_span (by simp))
  have hr : rightCoordinate t ∈ x.asIdeal := hx (Ideal.subset_span (by simp))
  rcases (charts_eq_iff R t n h hn x y).mp he with
    ⟨z, _, hz, _⟩ | ⟨z, _, hz, _⟩
  · have hm : x ∈ Set.range (leftBranchOpen R t) := ⟨z, hz⟩
    rw [leftBranchOpen_range] at hm
    exact hm hl
  · have hm : x ∈ Set.range (precedingBranch R t) := ⟨z, hz⟩
    rw [precedingBranch_range, rightBranchOpen_range] at hm
    exact hm hr

/-- The original chart image contains a node point in no other chart image. -/
theorem node_chart_mem_range_iff (i j : Fin n) (x : PolygonSmoothing.chart R t)
    (hx : coordinateIdeal t ≤ x.asIdeal) :
    chart R t n h i x ∈ Set.range (chart R t n h j) ↔ i = j := by
  constructor
  · rintro ⟨y, hy⟩
    exact node_chart_label_unique R t n h x y hx hy.symm
  · rintro rfl
    exact ⟨x, rfl⟩

end FLT.Mazur.PolygonInfinitesimal

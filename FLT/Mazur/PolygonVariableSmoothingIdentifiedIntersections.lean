/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonVariableSmoothingIntersections
public import FLT.Mazur.PolygonVariableSmoothingChartIdentification

/-!
# Exact intersections after identifying the full node parameters

The cyclic edge classification transports through the specified parameter
identifications without expanding any concrete coefficient construction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonVariableSmoothing
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (t : Fin n → R)
  [∀ i, Fact (IsNilpotent (t i))] (h : 2 ≤ n)

/-- Distinct identified charts retain both possible full cyclic intersections. -/
theorem identifiedCharts_eq_iff {i j : Fin n} (hne : i ≠ j)
    (a b : R) (ha : a = t i) (hb : b = t j)
    (x : PolygonSmoothing.chart R a) (y : PolygonSmoothing.chart R b) :
    chartWithParameter R n t h i a ha x = chartWithParameter R n t h j b hb y ↔
      (∃ z : branchTorus R, (finRotate n).symm i = j ∧
        leftBranchOpen R a z = x ∧ precedingBranch R b z = y) ∨
      (∃ z : branchTorus R, (finRotate n).symm j = i ∧
        precedingBranch R a z = x ∧ leftBranchOpen R b z = y) := by
  subst a
  subst b
  simp only [chartWithParameter, nodeParameterIso, eqToIso_refl, Iso.refl_hom,
    Category.id_comp]
  exact charts_eq_iff R n t h hne x y

end FLT.Mazur.PolygonVariableSmoothing

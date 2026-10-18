/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonVariableSmoothingChartIdentification

/-!
# Identified node charts preserve their coefficient base

The full chart with a proved parameter equality has the original coefficient
projection. This is independent of the other cyclic node parameters.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonVariableSmoothing
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (t : Fin n → R)
  [∀ i, Fact (IsNilpotent (t i))] (h : 2 ≤ n)

/-- Identifying a node parameter preserves the full structural map to the coefficient spectrum. -/
@[reassoc] theorem chartWithParameter_toBase (i : Fin n) (a : R) (ha : a = t i) :
    chartWithParameter R n t h i a ha ≫ toBase R n t h = chartStructure R a := by
  subst a
  simp only [chartWithParameter, nodeParameterIso, eqToIso_refl, Iso.refl_hom,
    Category.id_comp]
  exact chart_toBase R n t h i

end FLT.Mazur.PolygonVariableSmoothing

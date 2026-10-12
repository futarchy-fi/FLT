/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalRotation
public import FLT.Mazur.PolygonInfinitesimalSpecialFiber
public import FLT.Mazur.PolygonRotationNoFixedPoints

/-!
# Rotation on the original closed polygon charts

Transport from the zero-parameter family rotates exactly the original chart
labels. The explicit overlap relation excludes fixed points, including on
the two-gon where two distinct edges join the same pair of charts.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonCyclicAtlas
open PolygonInfinitesimal PolygonPinching
set_option backward.isDefEq.respectTransparency false
universe u
variable (K : Type u) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original closed polygon action transported through the actual zero-fiber comparison. -/
def closedRotation (a : ZMod n) : scheme K n h ⟶ scheme K n h :=
  (zeroFiberIso K n h).hom ≫ rotation K 0 n h a ≫ (zeroFiberIso K n h).inv

/-- Transport retains the actual original node chart with its translated label. -/
@[reassoc] theorem chart_closedRotation (a : ZMod n) (i : Fin n) :
    chart K n h i ≫ closedRotation K n h a = chart K n h (rotateIndex a i) := by
  simp only [closedRotation, chart_zeroFiberIso_assoc, chart_rotation_assoc]
  rw [← chart_zeroFiberIso_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The comparison intertwines the original closed action and the zero-parameter action. -/
@[reassoc] theorem closedRotation_zeroFiberIso (a : ZMod n) :
    closedRotation K n h a ≫ (zeroFiberIso K n h).hom =
      (zeroFiberIso K n h).hom ≫ rotation K 0 n h a := by
  simp only [closedRotation, Category.assoc, Iso.inv_hom_id, Category.comp_id]

omit [NeZero n] in
/-- Distinct labels cannot give the same point with the same node-chart coordinate. -/
theorem chart_same_coordinate_ne {i j : Fin n} (hij : i ≠ j)
    (x : PolygonNodeBranches.node K) : chart K n h i x ≠ chart K n h j x := by
  intro he
  obtain ⟨z, _, hl, hr⟩ | ⟨z, _, hr, hl⟩ := (charts_eq_iff K n h hij x x).mp he
  all_goals
    exact Set.disjoint_left.mp (PolygonNodeBranches.disjoint_ranges K)
      ⟨z, hl⟩ ⟨(ProjectiveLine.inversion K).hom z, hr⟩

/-- Every nonzero cyclic action is fixed-point free on the original closed polygon. -/
theorem closedRotation_ne_self (a : ZMod n) (ha : a ≠ 0) (x : scheme K n h) :
    closedRotation K n h a x ≠ x := by
  obtain ⟨i, z, rfl⟩ := charts_cover K n h x
  have he := congrArg (fun f ↦ f z) (chart_closedRotation K n h a i)
  exact fun hf ↦ chart_same_coordinate_ne K n h (rotateIndex_ne_self n a ha i) z
    (he.symm.trans hf)

end FLT.Mazur.PolygonCyclicAtlas

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCartesianPointDegree
public import FLT.Mazur.PolygonCompleteGenusOneFamily
public import FLT.Mazur.DivisorPowerH1Bound

/-!
# Actual cohomology bounds for powers of the original marked point

For every specified field fiber, O(mP) has Euler characteristic m and H1
dimension at most one. Thus its H0 dimension is either m or m+1. These
statements keep the original point; exact low-pole dimensions still require
eliminating the remaining H1, not merely the Euler-characteristic calculation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve FCurve.ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] {Y : Scheme}
  (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

include hs in
/-- Every actual field square has structure-sheaf Euler characteristic zero. -/
theorem completeCartesianField_structureEuler :
    curveEulerCharacteristic q (structureUnitModule Y) = 0 := by
  unfold curveEulerCharacteristic
  rw [(moduleScalarHUnitEquiv q 0).finrank_eq, (moduleScalarHUnitEquiv q 1).finrank_eq,
    finrank_H0_of_constantGlobalSections q
      (completeCartesianField_constantSections K n h L s p q hs),
    completeCartesianFieldH1_finrank K n h L s p q hs]
  decide

/-- The original point-power line has Euler characteristic equal to its exponent. -/
theorem completeCartesianPointLine_power_euler (i : Fin n) (m : ℕ) :
    curveEulerCharacteristic q
      (tensorPower (completeCartesianPointLine K n h s p q hs i) m) = (m : ℤ) := by
  have hd := completeCartesianPointLine_power_degree K n h L s p q hs i m
  unfold curveSheafDegree at hd
  rwa [completeCartesianField_structureEuler K n h L s p q hs, sub_zero] at hd

/-- Actual first cohomology of each original point power has dimension at most one. -/
theorem completeCartesianPointLine_power_h1_le (i : Fin n) (m : ℕ) :
    Module.finrank L
      (ModuleScalarH q (tensorPower (completeCartesianPointLine K n h s p q hs i) m) 1) ≤
        1 := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  let _ := completeCartesianPoint_isFinite K n h L s p q hs i
  have hb := divisorPower_h1_finrank_le q
    (completeCartesianMarking_relativeCartier K n h s p q hs i).1 m
  rw [show structureModule Y = structureUnitModule Y from rfl,
    (moduleScalarHUnitEquiv q 1).finrank_eq,
    completeCartesianFieldH1_finrank K n h L s p q hs] at hb
  exact hb

/-- The actual section dimension equals the exponent plus the remaining H1 dimension. -/
theorem completeCartesianPointLine_power_h0_eq (i : Fin n) (m : ℕ) :
    Module.finrank L
        (ModuleScalarH q (tensorPower (completeCartesianPointLine K n h s p q hs i) m) 0) =
      m + Module.finrank L
        (ModuleScalarH q (tensorPower (completeCartesianPointLine K n h s p q hs i) m) 1) := by
  have he := completeCartesianPointLine_power_euler K n h L s p q hs i m
  unfold curveEulerCharacteristic at he
  omega

/-- Exactly two dimensions remain possible before the low-pole vanishing calculation. -/
theorem completeCartesianPointLine_power_h0_cases (i : Fin n) (m : ℕ) :
    let d := Module.finrank L
      (ModuleScalarH q (tensorPower (completeCartesianPointLine K n h s p q hs i) m) 0)
    d = m ∨ d = m + 1 := by
  have he := completeCartesianPointLine_power_h0_eq K n h L s p q hs i m
  have hb := completeCartesianPointLine_power_h1_le K n h L s p q hs i m
  dsimp only
  omega

end FLT.Mazur.PolygonInfinitesimalStages

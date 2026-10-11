/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCartesianPointLine
public import FLT.Mazur.SectionSumFieldLength
public import FLT.Mazur.DivisorPowerEulerCharacteristic

/-!
# Degree of the original polygon single-point line

The actual retained section has length one over every field. Its positive line
has degree one and its powers have degree equal to the exponent, even on the
singular polygon fiber. These are computations on the specified square.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve FCurve.ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] {Y : Scheme}
  (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- The original point remains a finite divisor on the specified field fiber. -/
theorem completeCartesianPoint_isFinite (i : Fin n) :
    IsFinite ((completeCartesianMarking K n h s p q hs i).ker.subschemeι ≫ q) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  rw [← sectionImageIso_hom q _ (completeCartesianMarking_snd K n h s p q hs i)]
  infer_instance

/-- Each retained label has actual scheme length one. -/
theorem completeCartesianPoint_length (i : Fin n) :
    divisorFieldLength q (completeCartesianMarking K n h s p q hs i).ker = 1 := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  exact divisorFieldLength_section q _ (completeCartesianMarking_snd K n h s p q hs i)

/-- The positive single-point line has degree one for the original field structure map. -/
theorem completeCartesianPointLine_degree (i : Fin n) :
    curveSheafDegree q (completeCartesianPointLine K n h s p q hs i) = 1 := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  let _ := completeCartesianPoint_isFinite K n h L s p q hs i
  rw [completeCartesianPointLine, divisor_degree_eq_fieldLength,
    completeCartesianPoint_length, Nat.cast_one]

/-- Every tensor power has its exact expected degree, including the zeroth power. -/
theorem completeCartesianPointLine_power_degree (i : Fin n) (m : ℕ) :
    curveSheafDegree q (tensorPower (completeCartesianPointLine K n h s p q hs i) m) =
      (m : ℤ) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  let _ := completeCartesianPoint_isFinite K n h L s p q hs i
  rw [completeCartesianPointLine, curveSheafDegree_divisor_power,
    completeCartesianPoint_length, Nat.cast_one, mul_one]

end FLT.Mazur.PolygonInfinitesimalStages

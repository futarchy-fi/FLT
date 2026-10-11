/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointDimensions
public import FLT.Mazur.DivisorPowerHZeroTransition

/-!
# New sections at each positive pole step on the original field squares

Each positive step has a one-dimensional quotient by the preceding actual
divisor transition. In particular, pole-two and pole-three sections exist
outside the lower pole spaces. These are inputs to a pointed cubic
construction; no cubic relation or scheme presentation is asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

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

/-- The original point-power transition supplies the actual pole filtration. -/
def completeCartesianPointH0Step (i : Fin n) (m : ℕ) :
    ModuleScalarH q (tensorPower (completeCartesianPointLine K n h s p q hs i) m) 0 →ₗ[L]
      ModuleScalarH q (tensorPower (completeCartesianPointLine K n h s p q hs i) (m + 1)) 0 :=
  divisorPowerH0Step q (completeCartesianMarking_relativeCartier K n h s p q hs i).1 m

/-- The positive pole-step quotient is one-dimensional for the original marked point. -/
theorem completeCartesianPointH0Step_quotient_finrank (i : Fin n) (m : ℕ) (hm : 0 < m) :
    Module.finrank L (ModuleScalarH q
      (tensorPower (completeCartesianPointLine K n h s p q hs i) (m + 1)) 0 ⧸
        LinearMap.range (completeCartesianPointH0Step K n h L s p q hs i m)) = 1 := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  have he := divisorPowerH0Step_quotient_finrank q
    (completeCartesianMarking_relativeCartier K n h s p q hs i).1 m
  change Module.finrank L (_ ⧸ LinearMap.range
    (completeCartesianPointH0Step K n h L s p q hs i m)) +
    Module.finrank L (ModuleScalarH q
      (tensorPower (completeCartesianPointLine K n h s p q hs i) m) 0) =
    Module.finrank L (ModuleScalarH q
      (tensorPower (completeCartesianPointLine K n h s p q hs i) (m + 1)) 0) at he
  rw [completeCartesianPointPower_h0 K n h L s p q hs i m hm,
    completeCartesianPointPower_h0 K n h L s p q hs i (m + 1) (by omega)] at he
  omega

/-- Each positive pole step has a new original section, outside the lower pole image. -/
theorem exists_completeCartesianPoint_new_section (i : Fin n) (m : ℕ) (hm : 0 < m) :
    ∃ x, x ∉ LinearMap.range (completeCartesianPointH0Step K n h L s p q hs i m) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  apply exists_divisorPowerH0Step_not_mem_range q
    (completeCartesianMarking_relativeCartier K n h s p q hs i).1 m
  change Module.finrank L (ModuleScalarH q
    (tensorPower (completeCartesianPointLine K n h s p q hs i) m) 0) <
    Module.finrank L (ModuleScalarH q
      (tensorPower (completeCartesianPointLine K n h s p q hs i) (m + 1)) 0)
  rw [completeCartesianPointPower_h0 K n h L s p q hs i m hm,
    completeCartesianPointPower_h0 K n h L s p q hs i (m + 1) (by omega)]
  omega

/-- Choose an actual global section with a new pole at the given positive step. -/
def completeCartesianPointNewSection (i : Fin n) (m : ℕ) (hm : 0 < m) :
    Γ(tensorPower (completeCartesianPointLine K n h s p q hs i) (m + 1), ⊤) :=
  moduleScalarH0Equiv q _ (exists_completeCartesianPoint_new_section
    K n h L s p q hs i m hm).choose

/-- The chosen actual section is outside the preceding canonical pole space. -/
theorem completeCartesianPointNewSection_not_mem_range (i : Fin n) (m : ℕ) (hm : 0 < m) :
    (moduleScalarH0Equiv q _).symm
      (completeCartesianPointNewSection K n h L s p q hs i m hm) ∉
        LinearMap.range (completeCartesianPointH0Step K n h L s p q hs i m) := by
  simpa only [completeCartesianPointNewSection, LinearEquiv.symm_apply_apply] using
    (exists_completeCartesianPoint_new_section K n h L s p q hs i m hm).choose_spec

end FLT.Mazur.PolygonInfinitesimalStages

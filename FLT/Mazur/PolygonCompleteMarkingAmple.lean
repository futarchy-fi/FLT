/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteDivisorLine
public import FLT.Mazur.PolygonCompleteLineQuotient
public import FLT.Mazur.ClosedPointFiberAmple
public import FLT.Mazur.ProperOnlyAmpleFiberNeighborhood

/-!
# Ampleness of the actual complete marked divisor line

The original zeroth-stage boundary line is ample. Its canonical comparison
transports ampleness to the actual closed fiber, and properness over the local
power-series base spreads it to the complete family.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj family boundaryLine completeMarkingLine

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The actual marked line is ample on the original parameter closed subscheme. -/
theorem completeMarkingLine_closed_ample :
    AmpleLineBundle ((pullback (compatibleProjAdicIdeal K n h).subschemeι).obj
      (completeMarkingLine K n h)) := by
  have hs := (boundaryLine_ample K 0 n h).of_iso (completeMarkingLineStageIso K n h 0)
  let e := originalStageAdicIso K n h 0
  let j := (compatibleProjAdicIdeal K n h ^ (0 + 1)).subschemeι
  have hc : AmpleLineBundle ((pullback e.hom).obj
      ((pullback j).obj (completeMarkingLine K n h))) :=
    hs.of_iso ((pullbackComp e.hom j).app _ ≪≫
      (pullbackCongr (originalStageAdicIso_hom_ι K n h 0)).app _)
  have ha := (ampleLineBundle_pullback_iso_iff e.hom _).mp hc
  exact (congrArg (fun I : (exactVeroneseProj K n h).IdealSheafData ↦
    AmpleLineBundle ((pullback I.subschemeι).obj (completeMarkingLine K n h)))
      (pow_one (compatibleProjAdicIdeal K n h))).mp ha

/-- The original parameter ideal is precisely the maximal ideal of the complete base. -/
theorem completeParameterIdeal_eq_maximal :
    parameterIdeal K = IsLocalRing.maximalIdeal (PowerSeries K) := by
  rw [← PowerSeries.ker_coeff_eq_max_ideal]
  ext f
  exact (Ideal.mem_span_singleton).trans PowerSeries.X_dvd_iff

/-- The actual marked line is ample on the residue-field fiber. -/
theorem completeMarkingLine_closedFiber_ample :
    AmpleLineBundle ((pullback
      ((exactVeroneseProjToBase K n h).fiberι (IsLocalRing.closedPoint (PowerSeries K)))).obj
        (completeMarkingLine K n h)) := by
  let _ : (IsLocalRing.closedPoint (PowerSeries K)).asIdeal.IsMaximal :=
    inferInstanceAs (IsLocalRing.maximalIdeal (PowerSeries K)).IsMaximal
  apply (BaseAdicThickening.closedSource_ample_iff_fiber (R := .of (PowerSeries K))
    (IsLocalRing.closedPoint (PowerSeries K)) (exactVeroneseProjToBase K n h) _).mp
  have hc := completeMarkingLine_closed_ample K n h
  unfold compatibleProjAdicIdeal at hc
  rw [completeParameterIdeal_eq_maximal] at hc
  exact hc

/-- Properness spreads the original boundary ampleness to the actual complete marked line. -/
theorem completeMarkingLine_ample : AmpleLineBundle (completeMarkingLine K n h) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  obtain ⟨U, hU, _, ha⟩ := exists_ample_neighborhood_spectrum_proper
    (exactVeroneseProjToBase K n h) (IsLocalRing.closedPoint (PowerSeries K))
    (completeMarkingLine K n h) (completeMarkingLine_rankOne K n h)
    (completeMarkingLine_closedFiber_ample K n h)
  have he : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp hU
  rw [he, Scheme.Hom.preimage_top] at ha
  let _ : IsIso (⊤ : (exactVeroneseProj K n h).Opens).ι :=
    (exactVeroneseProj K n h).topIso.isIso_hom
  exact (ampleLineBundle_pullback_iso_iff _ _).mp ha

/-- The original complete marked divisor line is relatively ample over the complete base. -/
theorem completeMarkingLine_relativelyAmple :
    RelativelyAmpleLineBundle (exactVeroneseProjToBase K n h) (completeMarkingLine K n h) :=
  (completeMarkingLine_ample K n h).relative_of_affine _

end FLT.Mazur.PolygonInfinitesimalStages

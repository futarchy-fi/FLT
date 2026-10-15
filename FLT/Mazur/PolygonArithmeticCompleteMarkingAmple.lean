/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCompleteDivisorLine
public import FLT.Mazur.PolygonArithmeticAdicRealization
public import FLT.Mazur.PolygonArithmeticBoundaryAmple
public import FLT.Mazur.ClosedPointFiberAmple
public import FLT.Mazur.ProperOnlyAmpleFiberNeighborhood

/-!
# Ampleness of the actual complete marked divisor line

The original zeroth-stage boundary line is ample. Its canonical comparison
transports ampleness to the actual closed fiber, and properness over the local
arithmetic coefficient base spreads it to the complete family.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj family boundaryLine completeMarkingLine

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The actual marked line is ample on the original parameter closed subscheme. -/
theorem completeMarkingLine_closed_ample :
    AmpleLineBundle ((pullback
      (compatibleProjAdicIdeal A π hne hgen n h).subschemeι).obj
      (completeMarkingLine A π hne hgen n h)) := by
  have hs := (boundaryLine_ample A π hgen 0 n h).of_iso
    (completeMarkingLineStageIso A π hne hgen n h 0)
  let e := originalStageAdicIso A π hne hgen n h 0
  let j := (compatibleProjAdicIdeal A π hne hgen n h ^ (0 + 1)).subschemeι
  have hc : AmpleLineBundle ((pullback e.hom).obj
      ((pullback j).obj (completeMarkingLine A π hne hgen n h))) :=
    hs.of_iso ((pullbackComp e.hom j).app _ ≪≫
      (pullbackCongr (originalStageAdicIso_hom_ι A π hne hgen n h 0)).app _)
  have ha := (ampleLineBundle_pullback_iso_iff e.hom _).mp hc
  exact (congrArg (fun I : (exactVeroneseProj A π n h hne hgen).IdealSheafData ↦
    AmpleLineBundle ((pullback I.subschemeι).obj (completeMarkingLine A π hne hgen n h)))
      (pow_one (compatibleProjAdicIdeal A π hne hgen n h))).mp ha

/-- The actual marked line is ample on the residue-field fiber. -/
theorem completeMarkingLine_closedFiber_ample :
    AmpleLineBundle ((pullback
      ((exactVeroneseProjToBase A π n h hne hgen).fiberι (IsLocalRing.closedPoint A))).obj
        (completeMarkingLine A π hne hgen n h)) := by
  let _ : (IsLocalRing.closedPoint A).asIdeal.IsMaximal :=
    inferInstanceAs (IsLocalRing.maximalIdeal A).IsMaximal
  apply (BaseAdicThickening.closedSource_ample_iff_fiber (R := .of A)
    (IsLocalRing.closedPoint A) (exactVeroneseProjToBase A π n h hne hgen) _).mp
  have hc := completeMarkingLine_closed_ample A π hne hgen n h
  unfold compatibleProjAdicIdeal at hc
  rw [← hgen] at hc
  exact hc

/-- Properness spreads the original boundary ampleness to the actual complete marked line. -/
theorem completeMarkingLine_ample :
    AmpleLineBundle (completeMarkingLine A π hne hgen n h) := by
  let _ := exactVeroneseProjToBase_isProper A π n h hne hgen
  obtain ⟨U, hU, _, ha⟩ := exists_ample_neighborhood_spectrum_proper
    (exactVeroneseProjToBase A π n h hne hgen) (IsLocalRing.closedPoint A)
    (completeMarkingLine A π hne hgen n h) (completeMarkingLine_rankOne A π hne hgen n h)
    (completeMarkingLine_closedFiber_ample A π hne hgen n h)
  have he : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp hU
  rw [he, Scheme.Hom.preimage_top] at ha
  let _ : IsIso (⊤ : (exactVeroneseProj A π n h hne hgen).Opens).ι :=
    (exactVeroneseProj A π n h hne hgen).topIso.isIso_hom
  exact (ampleLineBundle_pullback_iso_iff _ _).mp ha

/-- The original complete marked divisor line is relatively ample over the complete base. -/
theorem completeMarkingLine_relativelyAmple :
    RelativelyAmpleLineBundle (exactVeroneseProjToBase A π n h hne hgen)
      (completeMarkingLine A π hne hgen n h) := by
  let _ := exactVeroneseProjToBase_isProper A π n h hne hgen
  exact (completeMarkingLine_ample A π hne hgen n h).relative_of_affine _

end FLT.Mazur.PolygonArithmeticStages

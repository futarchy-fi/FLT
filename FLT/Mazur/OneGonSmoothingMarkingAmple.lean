/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingGenusOneFamily
public import FLT.Mazur.OneGonSmoothingMarkingLine
public import FLT.Mazur.CurveDivisorAmpleSupport
public import FLT.Mazur.ProperOnlyAmpleFiberNeighborhood
public import FLT.Mazur.ClosedPointFiberAmple
public import FLT.Mazur.RelativeSectionAmpleBaseChange

/-!
# Ampleness of the actual infinity marking on the complete smoothing

On every field fiber the finite Cartier marking meets the unique component.
Properness spreads its ampleness from the closed fiber over the local base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open FCurve FCurve.CurveFiberHypotheses WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [Field K]

/-- The actual retained infinity line is ample on every field fiber. -/
theorem completeFiberMarkingLine_ample (L : Type) [Field L]
    (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K))) :
    AmpleLineBundle (fiberMarkingLine (PowerSeries.X : PowerSeries K) s) := by
  let t := (PowerSeries.X : PowerSeries K)
  let f := (family t).hom
  let q := pullback.snd f s
  let z := fiberMarking t s
  let _ := family_proper t
  let _ : IsProper q := inferInstanceAs (IsProper (pullback.snd f s))
  let _ := integralCurveFieldSquare_isIntegral (equation t) s _ q
    (IsPullback.of_hasPullback _ _)
  have hz : z ≫ q = 𝟙 _ := fiberMarking_snd t s
  let _ : IsFinite (z.ker.subschemeι ≫ q) := by
    rw [← sectionImageIso_hom q z hz]
    infer_instance
  have hc := completeCartesian_classified K L s _ q (IsPullback.of_hasPullback _ _)
  apply (divisor_ample_iff_meets_components q (fiberMarking_relativeCartier t s).1
    hc.pureDimension).mpr
  intro Z hZ
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
  subst Z
  rw [Set.inter_univ, support_section_ker q z hz]
  exact Set.range_nonempty _

/-- The pullback of the original line is ample on every actual field fiber. -/
theorem completeMarkingLine_field_ample (L : Type) [Field L]
    (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K))) :
    AmpleLineBundle ((Scheme.Modules.pullback
      (pullback.fst (family (PowerSeries.X : PowerSeries K)).hom s)).obj
        (markingLine (PowerSeries.X : PowerSeries K))) :=
  (completeFiberMarkingLine_ample K L s).of_iso (markingLineBaseChangeIso _ s)

/-- Properness over the complete local base makes the original infinity line ample. -/
theorem completeMarkingLine_ample :
    AmpleLineBundle (markingLine (PowerSeries.X : PowerSeries K)) := by
  let f := (family (PowerSeries.X : PowerSeries K)).hom
  let x := IsLocalRing.closedPoint (PowerSeries K)
  let _ := family_proper (PowerSeries.X : PowerSeries K)
  have ha : AmpleLineBundle ((Scheme.Modules.pullback (f.fiberι x)).obj
      (markingLine (PowerSeries.X : PowerSeries K))) :=
    completeMarkingLine_field_ample K _ ((Spec (.of (PowerSeries K))).fromSpecResidueField x)
  obtain ⟨U, hU, _, hA⟩ := exists_ample_neighborhood_spectrum_proper f x _
    (markingLine_rankOne _) ha
  have htop : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp hU
  rw [htop, Scheme.Hom.preimage_top] at hA
  let _ : IsIso (⊤ : (family (PowerSeries.X : PowerSeries K)).left.Opens).ι :=
    (family (PowerSeries.X : PowerSeries K)).left.topIso.isIso_hom
  exact (ampleLineBundle_pullback_iso_iff _ _).mp hA

/-- The original infinity marking line is relatively ample over the complete base. -/
theorem completeMarkingLine_relativelyAmple :
    RelativelyAmpleLineBundle (family (PowerSeries.X : PowerSeries K)).hom
      (markingLine (PowerSeries.X : PowerSeries K)) := by
  let _ := family_proper (PowerSeries.X : PowerSeries K)
  exact (completeMarkingLine_ample K).relative_of_affine _

/-- Every retained infinity line remains relatively ample after arbitrary base change. -/
theorem completeFiberMarkingLine_relativelyAmple {S : Scheme}
    (s : S ⟶ Spec (.of (PowerSeries K))) :
    RelativelyAmpleLineBundle (pullback.snd (family (PowerSeries.X : PowerSeries K)).hom s)
      (fiberMarkingLine (PowerSeries.X : PowerSeries K) s) := by
  let _ := family_proper (PowerSeries.X : PowerSeries K)
  exact ((completeMarkingLine_relativelyAmple K).baseChange s).of_iso
    (markingLineBaseChangeIso _ s).symm

end FLT.Mazur.OneGonSmoothing

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonClosedCubicOmittedConstant
public import FLT.Mazur.PolygonClosedCubicContractionDivisors
public import FLT.Mazur.PolygonSinglePointPowerNormalization
public import FLT.Mazur.SectionSumFieldLength
public import FLT.Mazur.DivisorPowerEulerCharacteristic

/-!
# The original cubic-origin line on the retained complete normalization component

Every powered origin ideal pulls back to the original unit-one point power.
The canonical positive-line comparison retains its section and has degree
exactly the exponent; in particular the cubic coefficient has degree three.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching WeierstrassIntegralChart FCurve PolygonDivisorNormalizationPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completeClosedFiberInclusion completePointToIntegralCubic
  divisorLineBundle

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "W" => completePointWeierstrassCurve K n h i
local notation "r" => closedPointComponentToOriginalCubic K n h i i
local notation "hP" => And.left (ProjectiveLineMarkedCharts.relativeCartier K 1)

/-- The entire original retained component has the exact marked-point origin power. -/
theorem closedPointRetained_origin_power (m : ℕ) :
    ((integralCurveZero W).ker ^ m).comap r = (markedPoint K 1).ker ^ m := by
  rw [closedPointComponentToOriginalCubic, Scheme.IdealSheafData.comap_comp,
    closedPointCubic_origin_power, closedPointMarking, idealSheaf_comap_pow]
  rw [section_ideal K n (by omega) p (PolygonCyclicAtlas.nodes K n h)
    (PolygonCyclicPushout.isPushout K n h (by omega)) 1 i]

/-- Canonical positive-line comparison on the complete retained projective line. -/
def closedPointRetainedOriginLineIso (m : ℕ) :
    (pullback r).obj (originDivisorLine W m) ≅
      ProjectiveLineMarkedSectionTransition.line K 1 m := by
  let _ := idealModulePullbackHom_isIso_of_cartier r
    (originIdealSheaf_power_effectiveCartier W m)
    (by rw [closedPointRetained_origin_power]; exact (hP).pow m)
  exact divisorLinePullbackIsoOfEq r (originIdealSheaf_power_effectiveCartier W m)
    ((hP).pow m) (closedPointRetained_origin_power K n h i m)

/-- The retained normalization comparison preserves the original canonical section. -/
theorem closedPointRetainedOriginLineIso_section (m : ℕ) :
    DivisorLineSectionCompatible r (originIdealSheaf_power_effectiveCartier W m)
      ((hP).pow m) (closedPointRetainedOriginLineIso K n h i m) := by
  let _ := idealModulePullbackHom_isIso_of_cartier r
    (originIdealSheaf_power_effectiveCartier W m)
    (by rw [closedPointRetained_origin_power]; exact (hP).pow m)
  rw [closedPointRetainedOriginLineIso]
  exact divisorLinePullbackIsoOfEq_compatible r (originIdealSheaf_power_effectiveCartier W m)
    ((hP).pow m) (closedPointRetained_origin_power K n h i m)

/-- The origin power has its exact degree on the complete retained normalization component. -/
theorem closedPointRetainedOriginLine_degree (m : ℕ) :
    curveSheafDegree (ProjectiveLine.toBase K) ((pullback r).obj (originDivisorLine W m)) =
      (m : ℤ) := by
  let _ : IsFinite ((markedPoint K 1).ker.subschemeι ≫ ProjectiveLine.toBase K) := by
    rw [← sectionImageIso_hom (ProjectiveLine.toBase K) _
      (ProjectiveLineMarkedCharts.point_base K 1)]
    infer_instance
  rw [curveSheafDegree_iso _ (closedPointRetainedOriginLineIso K n h i m)]
  change curveSheafDegree (ProjectiveLine.toBase K)
    (divisorLineBundle ((markedPoint K 1).ker ^ m) ((hP).pow m)) = _
  rw [curveSheafDegree_divisor_ideal_power (ProjectiveLine.toBase K) hP,
    divisor_degree_eq_fieldLength (ProjectiveLine.toBase K) hP,
    divisorFieldLength_section (ProjectiveLine.toBase K) _
      (ProjectiveLineMarkedCharts.point_base K 1), Nat.cast_one, mul_one]

/-- The retained cubic coefficient has degree three, with the original map and origin. -/
theorem closedPointRetainedOriginCube_degree :
    curveSheafDegree (ProjectiveLine.toBase K) ((pullback r).obj (originDivisorLine W 3)) = 3 :=
  closedPointRetainedOriginLine_degree K n h i 3

end FLT.Mazur.PolygonInfinitesimalStages

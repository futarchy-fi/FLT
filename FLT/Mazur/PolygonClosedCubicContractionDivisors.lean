/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonClosedCubicContractionCharts
public import FLT.Mazur.PolygonCompletePointOriginCartesianBaseChange
public import FLT.Mazur.PolygonCompletePointOriginPositiveLine
public import FLT.Mazur.DivisorLineSectionCompatibility

/-!
# Full marked divisors shared by the closed cubic and the contraction

On the entire original closed polygon, the cubic origin and the one-gon
marking pull back to the same original Cartier divisor in every degree.
Their positive lines are compared through the canonical ideal comparisons;
neither contraction is assumed flat and no radical ideal is substituted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart FCurve PolygonOneGonContraction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve divisorLineBundle closedPointContraction closedPointMarking
  completeClosedFiberInclusion completePointToIntegralCubic

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completeClosedFiberInclusion K n h ≫ completePointToIntegralCubic K n h i
local notation "d" => closedPointContraction K n h i
local notation "s" => closedPointMarking K n h i
local notation "t" => PolygonMarkedSections.sectionMap K 1 (PolygonAtlas.normalization K 1) 1 0
local notation "hS" => And.left (PolygonMarkedSections.section_cartier K n
  (PolygonCyclicAtlas.normalization K n h) (by omega) (PolygonCyclicAtlas.nodes K n h)
  (PolygonCyclicPushout.isPushout K n h (by omega)) 1 i)
local notation "hT" => And.left (PolygonMarkedSections.section_cartier K 1
  (PolygonAtlas.normalization K 1) (by decide) (PolygonAtlas.nodes K 1)
  (PolygonAtlas.isPushout K 1 (by decide)) 1 0)

/-- The original cubic origin retains the full marking ideal in every degree on the closed fiber. -/
theorem closedPointCubic_origin_power (m : ℕ) :
    ((integralCurveZero (W)).ker ^ m).comap (g) = (s).ker ^ m := by
  have H := completeCartesianPointToOriginalCubic_originPower K n h (completeClosedBase K)
    (completeClosedFiberInclusion K n h) (PolygonCyclicAtlas.toBase K n h)
    (completeClosedFiber_isPullback K n h) i m
  rw [closedPointMarking_eq_cartesian]
  exact H

/-- The actual one-gon contraction retains exactly the same powers of the original marking. -/
theorem closedPointContraction_marking_power (m : ℕ) :
    ((t).ker ^ m).comap (d) = (s).ker ^ m := by
  rw [idealSheaf_comap_pow, closedPointContraction, section_contraction_ideal, closedPointMarking]

/-- Both original maps pull back the full powered divisors to equal ideal sheaves. -/
theorem closedPointCubicContraction_power_ideals (m : ℕ) :
    ((integralCurveZero (W)).ker ^ m).comap (g) = ((t).ker ^ m).comap (d) := by
  rw [closedPointCubic_origin_power, closedPointContraction_marking_power]

/-- Every power of the original closed-fiber marking is Cartier. -/
theorem closedPointMarkingPower_cartier (m : ℕ) : EffectiveCartier ((s).ker ^ m) := by
  rw [closedPointMarking]
  exact (hS).pow m

/-- Every power of the original one-gon marking is Cartier. -/
theorem closedPointOneGonMarkingPower_cartier (m : ℕ) : EffectiveCartier ((t).ker ^ m) :=
  (hT).pow m

local notation "hP" => closedPointMarkingPower_cartier K n h i
local notation "hQ" => closedPointOneGonMarkingPower_cartier K

/-- Canonically compare the original pulled cubic-origin line with the original marking line. -/
def closedPointCubicOriginLineIso (m : ℕ) :
    (pullback (g)).obj (originDivisorLine (W) m) ≅
      divisorLineBundle ((s).ker ^ m) (hP m) := by
  let _ := idealModulePullbackHom_isIso_of_cartier (g)
    (originIdealSheaf_power_effectiveCartier (W) m)
    (by rw [closedPointCubic_origin_power]; exact hP m)
  exact divisorLinePullbackIsoOfEq (g) (originIdealSheaf_power_effectiveCartier (W) m)
    (hP m) (closedPointCubic_origin_power K n h i m)

/-- Canonically compare the contracted marking line with the same original marking line. -/
def closedPointContractionMarkingLineIso (m : ℕ) :
    (pullback (d)).obj (divisorLineBundle ((t).ker ^ m) (hQ m)) ≅
      divisorLineBundle ((s).ker ^ m) (hP m) := by
  let _ := idealModulePullbackHom_isIso_of_cartier (d) (hQ m)
    (by rw [closedPointContraction_marking_power]; exact hP m)
  exact divisorLinePullbackIsoOfEq (d) (hQ m) (hP m)
    (closedPointContraction_marking_power K n h i m)

/-- The cubic line comparison preserves the original canonical vanishing section. -/
@[reassoc] theorem closedPointCubicOriginLineIso_section (m : ℕ) :
    (pullback (g)).map (divisorSectionMap (originIdealSheaf_power_effectiveCartier (W) m)) ≫
      (closedPointCubicOriginLineIso K n h i m).hom =
        (modulePullbackUnitIso (g)).hom ≫ divisorSectionMap (hP m) := by
  let _ := idealModulePullbackHom_isIso_of_cartier (g)
    (originIdealSheaf_power_effectiveCartier (W) m)
    (by rw [closedPointCubic_origin_power]; exact hP m)
  exact divisorLinePullbackIsoOfEq_section (g) (originIdealSheaf_power_effectiveCartier (W) m)
    (hP m) (closedPointCubic_origin_power K n h i m)

/-- The contraction line comparison preserves the same canonical vanishing section. -/
theorem closedPointContractionMarkingLineIso_section (m : ℕ) :
    DivisorLineSectionCompatible (d) (hQ m) (hP m)
      (closedPointContractionMarkingLineIso K n h i m) := by
  let _ := idealModulePullbackHom_isIso_of_cartier (d) (hQ m)
    (by rw [closedPointContraction_marking_power]; exact hP m)
  rw [closedPointContractionMarkingLineIso]
  exact divisorLinePullbackIsoOfEq_compatible (d) (hQ m) (hP m)
    (closedPointContraction_marking_power K n h i m)

/-- The positive line comparison on the whole closed polygon in every degree. -/
def closedPointCubicContractionLineIso (m : ℕ) :
    (pullback (g)).obj (originDivisorLine (W) m) ≅
      (pullback (d)).obj (divisorLineBundle ((t).ker ^ m) (hQ m)) :=
  closedPointCubicOriginLineIso K n h i m ≪≫
    (closedPointContractionMarkingLineIso K n h i m).symm

end FLT.Mazur.PolygonInfinitesimalStages

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomSubgroupVanishingChart
public import FLT.Mazur.FiniteFlatIdealVanishingGluing
public import FLT.Mazur.FiniteFlatIdealVanishingZero

/-!
# The global closed multiplication locus for cyclic parameters

The full multiplication ideal on the actual divisor product gives a global
closed locus, covered by the previously constructed coefficient charts.
The universal specialization lives on the original auxiliary parameter
scheme. Compatibility of the cyclic family with arbitrary parameter pullback
is still needed to give its universal subgroup interpretation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme} (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)

/-- The actual global coefficient ideal of the full multiplication obstruction. -/
def cyclicHomCoefficientIdealSheaf : T.IdealSheafData :=
  FiniteFlatIdealVanishing.idealSheaf
    (cyclicHomDivisorProduct n f).hom (cyclicHomMultiplicationIdeal n f)

/-- The glued closed locus of the original multiplication equations. -/
def cyclicHomMultiplicationLocus : Scheme :=
  FiniteFlatIdealVanishing.locus
    (cyclicHomDivisorProduct n f).hom (cyclicHomMultiplicationIdeal n f)

/-- The original immersion of the multiplication locus into its parameter scheme. -/
def cyclicHomMultiplicationLocusInclusion : cyclicHomMultiplicationLocus n f ⟶ T :=
  FiniteFlatIdealVanishing.locusInclusion
    (cyclicHomDivisorProduct n f).hom (cyclicHomMultiplicationIdeal n f)

instance cyclicHomMultiplicationLocusInclusion_closed :
    IsClosedImmersion (cyclicHomMultiplicationLocusInclusion n f) :=
  FiniteFlatIdealVanishing.locusInclusion_closed _ _

/-- Every original coefficient chart is a chart of the global multiplication locus. -/
def cyclicHomSubgroupChartToLocus (U : T.affineOpens) :
    cyclicHomSubgroupChart n f U ⟶ cyclicHomMultiplicationLocus n f :=
  FiniteFlatIdealVanishing.chartToLocus _ _ U

/-- The existing coefficient chart is the actual pullback of the global immersion. -/
theorem cyclicHomSubgroupChart_isPullback (U : T.affineOpens) :
    IsPullback (cyclicHomSubgroupChartInclusion n f U) (cyclicHomSubgroupChartToLocus n f U)
      U.2.fromSpec (cyclicHomMultiplicationLocusInclusion n f) :=
  FiniteFlatIdealVanishing.chart_isPullback _ _ U

/-- The whole parameter scheme satisfies the equations exactly when its locus is the whole base. -/
theorem cyclicHomMultiplicationLocus_isIso_iff :
    IsIso (cyclicHomMultiplicationLocusInclusion n f) ↔
      cyclicHomMultiplicationEquation n f = 0 := by
  rw [cyclicHomMultiplicationEquation_iff_ideal]
  exact FiniteFlatIdealVanishing.locusInclusion_isIso_iff _ _

/-- The global closed equation locus on the original universal auxiliary parameter scheme. -/
def cyclicHomUniversalMultiplicationLocus : Scheme := cyclicHomMultiplicationLocus n (𝟙 _)

/-- Its original global closed immersion into the universal parameter scheme. -/
def cyclicHomUniversalMultiplicationLocusInclusion :
    cyclicHomUniversalMultiplicationLocus n ⟶ (cyclicHomAuxiliaryScheme n).left :=
  cyclicHomMultiplicationLocusInclusion n (𝟙 _)

end FLT.Mazur.UniversalWeierstrass

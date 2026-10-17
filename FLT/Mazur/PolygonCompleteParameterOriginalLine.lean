/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteParameterLineCocycle
public import FLT.Mazur.DivisorLineSectionIdealTransport

/-!
# Varying translations compare to the original complete marking line

The unit moved line is canonically the existing original base-changed marking
line. Translation comparisons preserve its actual canonical divisor section.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] completeSmoothGrpObj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "M" => completeOriginalSmoothOver K n h
variable {T : Over (Spec (.of (PowerSeries K)))}

/-- The unit moved ideal is the full product of the existing original lifted markings. -/
theorem completeParameterMovedIdeal_unit_original :
    completeParameterMovedIdeal K n h (1 : T ⟶ (M)) =
      ∏ i : Fin n, (completeFiberMarking K n h T.hom i).ker :=
  (completeParameterMovedIdeal_one K n h).trans (completeMarkingDivisor_comap K n h T.hom)

/-- The actual unit moved line identifies canonically with the original base-changed line. -/
def completeParameterMovedLineUnitIso :
    completeParameterMovedLine K n h (1 : T ⟶ (M)) ≅ completeFiberMarkingLine K n h T.hom :=
  divisorLineBundleEqIso (completeParameterMovedIdeal_unit_original K n h)
    (completeParameterMovedIdeal_cartier K n h 1).1
    (completeFiberMarkingDivisor_relativeCartier K n h T.hom).1

/-- Translation compares the moved positive line with the existing original marking line. -/
def completeParameterOriginalLineIso (g : T ⟶ (M)) :
    (Scheme.Modules.pullback (completeParameterTranslation K n h g).left).obj
      (completeParameterMovedLine K n h g) ≅ completeFiberMarkingLine K n h T.hom :=
  completeParameterMovedLineIso K n h g 1 g (_root_.mul_one g) ≪≫
    completeParameterMovedLineUnitIso K n h

/-- The original marking section is retained by the actual varying-parameter comparison. -/
theorem completeParameterOriginalLineIso_section (g : T ⟶ (M)) :
    DivisorLineSectionCompatible (completeParameterTranslation K n h g).left
      (completeParameterMovedIdeal_cartier K n h g).1
      (completeFiberMarkingDivisor_relativeCartier K n h T.hom).1
      (completeParameterOriginalLineIso K n h g) :=
  (completeParameterMovedLineIso_section K n h g 1 g (_root_.mul_one g)).targetIdealEq
    (completeParameterMovedIdeal_unit_original K n h)

/-- All tensor powers retain the existing original marking section. -/
theorem completeParameterOriginalLineIso_power_section (g : T ⟶ (M)) (d : ℕ) :
    DivisorLinePowerSectionCompatible (completeParameterTranslation K n h g).left
      (completeParameterMovedIdeal_cartier K n h g).1
      (completeFiberMarkingDivisor_relativeCartier K n h T.hom).1
      (completeParameterOriginalLineIso K n h g) d :=
  (completeParameterOriginalLineIso_section K n h g).tensorPower_section d

end FLT.Mazur.PolygonInfinitesimalStages

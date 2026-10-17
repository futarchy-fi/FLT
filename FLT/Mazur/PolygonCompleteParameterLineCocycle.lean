/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteParameterMarkingLine
public import FLT.Mazur.DivisorLineSectionIdentity
public import FLT.Mazur.DivisorLineSectionTriangle
public import FLT.Mazur.DivisorLineTensorSectionCompatibility

/-!
# Coherent moved marking lines on the original parameter families

Identity and composition use the actual sheaf pullback unitor and compositor.
The same equations and canonical sections persist in every tensor degree.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  tensorPowerPullbackComparison
attribute [local instance] completeSmoothGrpObj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "M" => completeOriginalSmoothOver K n h
local notation "t" => completeParameterTranslation K n h
local notation "e" => completeParameterMovedLineIso K n h
variable {T : Over (Spec (.of (PowerSeries K)))}

/-- The identity parameter gives exactly the pullback unitor on every moved line. -/
theorem completeParameterMovedLineIso_one (k : T ⟶ (M)) :
    (e) 1 k k (_root_.one_mul k) =
      (Scheme.Modules.pullbackCongr
        (congrArg Over.Hom.left (completeParameterTranslation_one K n h (T := T)))).app
          (completeParameterMovedLine K n h k) ≪≫
      (Scheme.Modules.pullbackId _).app (completeParameterMovedLine K n h k) :=
  (completeParameterMovedLineIso_section K n h 1 k k (_root_.one_mul k)).eq_id
    (congrArg Over.Hom.left (completeParameterTranslation_one K n h (T := T)))

/-- Successive original translations satisfy the actual moved marking-line cocycle. -/
theorem completeParameterMovedLineIso_cocycle (g k l : T ⟶ (M)) :
    LinePullbackTriangle ((t) k).left ((t) g).left ((t) (g * k)).left
      (congrArg Over.Hom.left (completeParameterTranslation_mul K n h g k).symm)
      ((e) g (k * l) ((g * k) * l) (_root_.mul_assoc g k l).symm)
      ((e) k l (k * l) rfl) ((e) (g * k) l ((g * k) * l) rfl) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (completeParameterMovedLineIso_section K n h g (k * l) ((g * k) * l)
      (_root_.mul_assoc g k l).symm)
    (completeParameterMovedLineIso_section K n h k l (k * l) rfl)
    (completeParameterMovedLineIso_section K n h (g * k) l ((g * k) * l) rfl)

/-- Every tensor degree retains the original compositor cocycle. -/
theorem completeParameterMovedLineIso_power_cocycle (g k l : T ⟶ (M)) (d : ℕ) :
    LinePullbackTriangle ((t) k).left ((t) g).left ((t) (g * k)).left
      (congrArg Over.Hom.left (completeParameterTranslation_mul K n h g k).symm)
      (tensorPowerPullbackComparison _
        ((e) g (k * l) ((g * k) * l) (_root_.mul_assoc g k l).symm) d)
      (tensorPowerPullbackComparison _ ((e) k l (k * l) rfl) d)
      (tensorPowerPullbackComparison _ ((e) (g * k) l ((g * k) * l) rfl) d) :=
  (completeParameterMovedLineIso_cocycle K n h g k l).tensorPower d

/-- Every powered comparison preserves its actual powered marking section. -/
theorem completeParameterMovedLineIso_power_section
    (g k r : T ⟶ (M)) (w : g * k = r) (d : ℕ) :
    DivisorLinePowerSectionCompatible ((t) g).left
      (completeParameterMovedIdeal_cartier K n h r).1
      (completeParameterMovedIdeal_cartier K n h k).1 ((e) g k r w) d :=
  (completeParameterMovedLineIso_section K n h g k r w).tensorPower_section d

end FLT.Mazur.PolygonInfinitesimalStages

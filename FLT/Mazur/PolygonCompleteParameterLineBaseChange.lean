/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteParameterBaseChange
public import FLT.Mazur.PolygonCompleteParameterLineCocycle

/-!
# Base-change coherence for varying original marking-line comparisons

The original translation comparisons commute with arbitrary parameter change
as actual section-preserving sheaf isomorphisms, in every tensor degree.
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
local notation "X" => completeOriginalWholeOver K n h
local notation "t" => completeParameterTranslation K n h
local notation "e" => completeParameterMovedLineIso K n h
local notation "b" => completeParameterMovedLineBaseChangeIso K n h
variable {U T : Over (Spec (.of (PowerSeries K)))} (f : U ⟶ T)

/-- Translation and base change commute on the actual moved marking lines. -/
theorem completeParameterMovedLineIso_baseChange (g k : T ⟶ (M)) :
    LinePullbackSquare (𝟙 (X) ⊗ₘ f).left ((t) g).left
      ((t) (f ≫ g)).left (𝟙 (X) ⊗ₘ f).left
      (congrArg Over.Hom.left (completeParameterTranslation_baseChange K n h f g))
      ((e) g k (g * k) rfl) ((b) f k) ((b) f (g * k))
      ((e) (f ≫ g) (f ≫ k) (f ≫ (g * k)) (MonObj.comp_mul f g k).symm) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (completeParameterMovedLineIso_section K n h g k (g * k) rfl)
    (completeParameterMovedLineBaseChangeIso_section K n h f k)
    (completeParameterMovedLineBaseChangeIso_section K n h f (g * k))
    (completeParameterMovedLineIso_section K n h (f ≫ g) (f ≫ k) (f ≫ (g * k))
      (MonObj.comp_mul f g k).symm)

/-- Every powered original line comparison retains the same base-change square. -/
theorem completeParameterMovedLineIso_power_baseChange (g k : T ⟶ (M)) (d : ℕ) :
    LinePullbackSquare (𝟙 (X) ⊗ₘ f).left ((t) g).left
      ((t) (f ≫ g)).left (𝟙 (X) ⊗ₘ f).left
      (congrArg Over.Hom.left (completeParameterTranslation_baseChange K n h f g))
      (tensorPowerPullbackComparison _ ((e) g k (g * k) rfl) d)
      (tensorPowerPullbackComparison _ ((b) f k) d)
      (tensorPowerPullbackComparison _ ((b) f (g * k)) d)
      (tensorPowerPullbackComparison _
        ((e) (f ≫ g) (f ≫ k) (f ≫ (g * k)) (MonObj.comp_mul f g k).symm) d) :=
  (completeParameterMovedLineIso_baseChange K n h f g k).tensorPower d

/-- Every powered parameter-change comparison preserves the original moved section. -/
theorem completeParameterMovedLineBaseChangeIso_power_section (g : T ⟶ (M)) (d : ℕ) :
    DivisorLinePowerSectionCompatible (𝟙 (X) ⊗ₘ f).left
      (completeParameterMovedIdeal_cartier K n h g).1
      (completeParameterMovedIdeal_cartier K n h (f ≫ g)).1 ((b) f g) d :=
  (completeParameterMovedLineBaseChangeIso_section K n h f g).tensorPower_section d

end FLT.Mazur.PolygonInfinitesimalStages

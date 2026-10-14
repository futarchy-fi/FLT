/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointOriginCartesian
public import FLT.Mazur.CartierIdealPullbackComparison
public import FLT.Mazur.WeierstrassOriginDivisorPullback

/-!
# Original positive divisor lines along the complete-base cubic map

The original marking-ideal equality supplies the canonical comparison for every
positive origin power, without assuming flatness of the contraction morphism.
The comparison preserves the original canonical section maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "s" => completeBaseMarking K n h i
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "V" => completePointOriginOpen K n h i
local notation "q" => completePointToOrigin K n h i

local notation "J" => completePointPulledOriginIdeal K n h i

local notation "hI" => completePointFirstOrderCartier K n h i

/-- The pulled origin power is effective Cartier because it is the original marking power. -/
theorem completePointToIntegralCubic_origin_power_cartier (m : ℕ) :
    EffectiveCartier (((integralCurveZero (W)).ker ^ m).comap (g)) := by
  rw [completePointToIntegralCubic_origin_power]
  exact (hI).pow m

/-- The canonical ideal-module comparison is invertible for every original origin power. -/
theorem completePointToIntegralCubic_origin_power_ideal_isIso (m : ℕ) :
    IsIso (idealModulePullbackHom ((integralCurveZero (W)).ker ^ m) (g)) :=
  idealModulePullbackHom_isIso_of_cartier (g) (originIdealSheaf_power_effectiveCartier (W) m)
    (completePointToIntegralCubic_origin_power_cartier K n h i m)

/-- The genuine pulled positive origin power is the dual original marking power. -/
def completePointOriginPositiveLineIso (m : ℕ) :
    (pullback (g)).obj (originDivisorLine (W) m) ≅
      divisorLineBundle ((s).ker ^ m) ((hI).pow m) := by
  let _ := completePointToIntegralCubic_origin_power_ideal_isIso K n h i m
  exact divisorLinePullbackIsoOfEq (g) (originIdealSheaf_power_effectiveCartier (W) m)
    ((hI).pow m) (completePointToIntegralCubic_origin_power K n h i m)

/-- The positive-line comparison retains the actual canonical section morphism. -/
@[reassoc] theorem completePointOriginPositiveLineIso_section (m : ℕ) :
    (pullback (g)).map (divisorSectionMap (originIdealSheaf_power_effectiveCartier (W) m)) ≫
      (completePointOriginPositiveLineIso K n h i m).hom =
        (modulePullbackUnitIso (g)).hom ≫ divisorSectionMap ((hI).pow m) := by
  let _ := completePointToIntegralCubic_origin_power_ideal_isIso K n h i m
  exact divisorLinePullbackIsoOfEq_section (g) (originIdealSheaf_power_effectiveCartier (W) m)
    ((hI).pow m) (completePointToIntegralCubic_origin_power K n h i m)

/-- The original tensor-power line is recovered from the actual cubic-origin power. -/
def completePointOriginTensorLineIso (m : ℕ) :
    (pullback (g)).obj (originDivisorLine (W) m) ≅
      tensorPower (completePointLine K n h i) m :=
  completePointOriginPositiveLineIso K n h i m ≪≫ (divisorLineBundlePowerIso (hI) m).symm

end FLT.Mazur.PolygonInfinitesimalStages

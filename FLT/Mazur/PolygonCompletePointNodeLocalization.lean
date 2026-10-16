/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOriginalNodeBasicOpen

/-!
# The particular complete pole functions in the original chart localization

Restriction to D((1-x)(1-y)) gives elements of the original smoothing algebra
localized at that explicit denominator. No new pole sections or frames are chosen.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i j : Fin n)

/-- The original full-stage node chart localized away from its two unit markings. -/
abbrev StageNodeLocalization := Localization.Away (nodeMarkingDenominator (parameter K m))

/-- The explicit localized chart maps into the domain of the retained pole functions. -/
def completePointNodeLocalizationChart :
    Spec (.of (StageNodeLocalization K m)) ⟶
      (completePointStageNodeOpen K n h m i j).toScheme :=
  (basicOpenIsoSpecAway (R := .of (ChartRing (parameter K m)))
    (nodeMarkingDenominator (parameter K m))).inv ≫
    (PolygonSmoothing.chart (Ring K m) (parameter K m)).homOfLE
      (nodeMarkingBasicOpen_le_completePointStageNodeOpen K m n h i j)

omit [NeZero n] in
/-- This chart map retains the original localization map on the full arithmetic chart. -/
theorem completePointNodeLocalizationChart_ι :
    completePointNodeLocalizationChart K n h m i j ≫
      (completePointStageNodeOpen K n h m i j).ι =
        Spec.map (CommRingCat.ofHom
          (algebraMap (ChartRing (parameter K m)) (StageNodeLocalization K m))) := by
  simp only [completePointNodeLocalizationChart, Category.assoc, Scheme.homOfLE_ι]
  rw [← basicOpenIsoSpecAway_hom_SpecMap (R := .of (ChartRing (parameter K m)))
    (nodeMarkingDenominator (parameter K m)), Iso.inv_hom_id_assoc]

/-- Actual restriction of regular functions into the original node localization. -/
def completePointNodeLocalizationMap :
    Γ((completePointStageNodeOpen K n h m i j).toScheme, ⊤) →+*
      StageNodeLocalization K m :=
  (Scheme.ΓSpecIso (.of (StageNodeLocalization K m))).hom.hom.comp
    (completePointNodeLocalizationChart K n h m i j).appTop.hom

/-- The particular original order-two function in explicit localized chart coordinates. -/
def completePointNodeLocalizedPoleTwo : StageNodeLocalization K m :=
  completePointNodeLocalizationMap K n h m i j
    (completePointStageNodePoleTwo K n h m i j)

/-- The particular original order-three function in the same localized chart coordinates. -/
def completePointNodeLocalizedPoleThree : StageNodeLocalization K m :=
  completePointNodeLocalizationMap K n h m i j
    (completePointStageNodePoleThree K n h m i j)

/-- The localized original cubic has exactly the same particular pole representatives. -/
theorem completePointNodeLocalizedCubic_coordinates (k : Fin 3) :
    completePointNodeLocalizationMap K n h m i j
      (completePointStageNodeCubic K n h m i j k) =
        ![completePointNodeLocalizedPoleTwo K n h m i j,
          completePointNodeLocalizedPoleThree K n h m i j, 1] k := by
  rw [completePointStageNodeCubic_coordinates]
  fin_cases k
  · rfl
  · rfl
  · exact map_one _

end FLT.Mazur.PolygonInfinitesimalStages

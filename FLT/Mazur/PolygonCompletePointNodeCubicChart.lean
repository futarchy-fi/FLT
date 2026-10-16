/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointNodeLocalization
public import FLT.Mazur.PolygonCompletePointStageNodeRatios
public import FLT.Mazur.PolygonCompletePointCubicChartRatios
public import FLT.Mazur.ModuleSectionProjectiveChartNaturality

/-!
# The actual complete cubic chart on the original localized node

The retained pole functions are the coordinate homomorphism of the
unchanged complete cubic contraction on the full localized stage chart.
This supplies a geometric comparison, including every stage nilpotent.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing FCurve ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i j : Fin n)
local notation "f" => originalStageToCompatibleProj K n h m
local notation "a" => PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h j
local notation "C" => GlobalIdealPowerCompatibility.complement
  (Scheme.Hom.ker (marking K m n h i))
local notation "L" => tensorPower (completePointLine K n h i) 3
local notation "s" => completePointProjectiveSections K n h i
local notation "O" => sectionGeneratorOpen (L) (s 2)
local notation "E" => completePointWeierstrassCurve K n h i
local notation "N" => completePointNodeLocalizationChart K n h m i j
local notation "η" => algebraMap (ChartRing (parameter K m)) (StageNodeLocalization K m)

/-- The original node localization maps into the actual complete affine Z cubic chart. -/
def completePointNodeToCubicChart :
    Spec (.of (StageNodeLocalization K m)) ⟶ Spec (.of (Coordinate (E) 2)) :=
  (N) ≫ ((a) ∣_ (C)) ≫
    (f).resLE (O) (C) (completePointStageComplement_preimage K n h m i).le ≫
      completePointToCubicChart K n h i 2

/-- This affine chart retains the original full contraction after including into the cubic. -/
@[reassoc] theorem completePointNodeToCubicChart_inclusion :
    completePointNodeToCubicChart K n h m i j ≫ integralCurveChart (E) 2 =
      Spec.map (CommRingCat.ofHom (η)) ≫ (a) ≫ (f) ≫
        completePointToIntegralCubic K n h i := by
  let g := (f).resLE (O) (C) (completePointStageComplement_preimage K n h m i).le
  calc
    _ = (N) ≫ ((a) ∣_ (C)) ≫ g ≫ (O).ι ≫
        completePointToIntegralCubic K n h i := by
      simpa only [completePointNodeToCubicChart, g, completePointLine, Category.assoc] using
        congrArg (fun z ↦ (N) ≫ ((a) ∣_ (C)) ≫ g ≫ z)
          (completePointToCubicChart_inclusion K n h i 2)
    _ = (N) ≫ ((a) ∣_ (C)) ≫ (C).ι ≫ (f) ≫
        completePointToIntegralCubic K n h i := by
      simpa only [g, Category.assoc] using
        congrArg (fun z ↦ (N) ≫ ((a) ∣_ (C)) ≫ z ≫ completePointToIntegralCubic K n h i)
          (Scheme.Hom.resLE_comp_ι (f)
            (completePointStageComplement_preimage K n h m i).le)
    _ = (N) ≫ (completePointStageNodeOpen K n h m i j).ι ≫ (a) ≫ (f) ≫
        completePointToIntegralCubic K n h i := by
      simpa only [completePointStageNodeOpen, Category.assoc] using
        congrArg (fun z ↦ (N) ≫ z ≫ (f) ≫ completePointToIntegralCubic K n h i)
          (morphismRestrict_ι (a) (C))
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ z ≫ (a) ≫ (f) ≫ completePointToIntegralCubic K n h i)
          (completePointNodeLocalizationChart_ι K n h m i j)

/-- The actual complete cubic coordinate map on the unchanged localized node ring. -/
def completePointNodeCubicFunctions : Coordinate (E) 2 →+* StageNodeLocalization K m :=
  (Scheme.ΓSpecIso (.of (StageNodeLocalization K m))).hom.hom.comp
    ((completePointNodeToCubicChart K n h m i j).appTop.hom.comp
      (Scheme.ΓSpecIso (.of (Coordinate (E) 2))).inv.hom)

/-- Its three original normalized coordinates are precisely the retained pole functions. -/
theorem completePointNodeCubicFunctions_coordinate (k : Fin 3) :
    completePointNodeCubicFunctions K n h m i j (coord (E) 2 k) =
      ![completePointNodeLocalizedPoleTwo K n h m i j,
        completePointNodeLocalizedPoleThree K n h m i j, 1] k := by
  let g := (f).resLE (O) (C) (completePointStageComplement_preimage K n h m i).le
  let r := sectionRatioOn (L) (s 2) (O) le_rfl (s k)
  have h₁ := congrArg (fun z : Γ((O).toScheme, ⊤) ↦
    completePointNodeLocalizationMap K n h m i j (((a) ∣_ (C)).appTop (g.appTop z)))
      (completePointToCubicChart_coordinate K n h i 2 k)
  have h₂ := congrArg (fun z : Γ((C).toScheme, ⊤) ↦
    completePointNodeLocalizationMap K n h m i j (((a) ∣_ (C)).appTop z))
      (resLE_topIso_inv (f) (O) (C)
        (completePointStageComplement_preimage K n h m i).le r)
  have h₃ := congrArg (completePointNodeLocalizationMap K n h m i j)
    (completePointStageNodeCubic_completeRatio K n h m i j k)
  have he := h₁.trans (h₂.trans (h₃.symm.trans
    (completePointNodeLocalizedCubic_coordinates K n h m i j k)))
  simpa only [completePointNodeCubicFunctions, completePointNodeToCubicChart, g,
    completePointNodeLocalizationMap, RingHom.comp_apply, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, CommRingCat.Hom.hom, completePointLine,
    completePointStageNodeOpen] using he

end FLT.Mazur.PolygonInfinitesimalStages

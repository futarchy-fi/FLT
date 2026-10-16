/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointNodeComplementNumerators
public import FLT.Mazur.PolygonCompletePointStageNodeRatios
public import FLT.Mazur.PolygonCompletePointCubicChartRatios
public import FLT.Mazur.ModuleSectionProjectiveChartNaturality

/-!
# The complete cubic chart on the entire marking complement

The actual complement maps to the cubic Z chart, with the retained pole
functions as coordinates. No incoming marking denominator is inverted.
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
local notation "N" => completePointStageNodeOpen K n h m i j

/-- The full stage marking complement maps into the actual complete cubic Z chart. -/
def completePointStageComplementToCubicChart :
    (N).toScheme ⟶ Spec (.of (Coordinate (E) 2)) :=
  ((a) ∣_ (C)) ≫
    (f).resLE (O) (C) (completePointStageComplement_preimage K n h m i).le ≫
      completePointToCubicChart K n h i 2

/-- This affine chart retains the original full contraction after including into the cubic. -/
@[reassoc] theorem completePointStageComplementToCubicChart_inclusion :
    completePointStageComplementToCubicChart K n h m i j ≫ integralCurveChart (E) 2 =
      (N).ι ≫ (a) ≫ (f) ≫
        completePointToIntegralCubic K n h i := by
  let g := (f).resLE (O) (C) (completePointStageComplement_preimage K n h m i).le
  calc
    _ = ((a) ∣_ (C)) ≫ g ≫ (O).ι ≫ completePointToIntegralCubic K n h i := by
      simpa only [completePointStageComplementToCubicChart, g, completePointLine,
        Category.assoc] using
        congrArg (fun z ↦ ((a) ∣_ (C)) ≫ g ≫ z)
          (completePointToCubicChart_inclusion K n h i 2)
    _ = ((a) ∣_ (C)) ≫ (C).ι ≫ (f) ≫ completePointToIntegralCubic K n h i := by
      simpa only [g, Category.assoc] using
        congrArg (fun z ↦ ((a) ∣_ (C)) ≫ z ≫ completePointToIntegralCubic K n h i)
          (Scheme.Hom.resLE_comp_ι (f)
            (completePointStageComplement_preimage K n h m i).le)
    _ = _ := by
      simpa only [completePointStageNodeOpen, Category.assoc] using
        congrArg (fun z ↦ z ≫ (f) ≫ completePointToIntegralCubic K n h i)
          (morphismRestrict_ι (a) (C))

/-- The coordinate homomorphism takes values in the entire marking complement. -/
def completePointStageComplementCubicFunctions : Coordinate (E) 2 →+* Γ((N).toScheme, ⊤) :=
  (completePointStageComplementToCubicChart K n h m i j).appTop.hom.comp
    (Scheme.ΓSpecIso (.of (Coordinate (E) 2))).inv.hom

/-- Its normalized coordinates are the original retained complement functions. -/
theorem completePointStageComplementCubicFunctions_coordinate (k : Fin 3) :
    completePointStageComplementCubicFunctions K n h m i j (coord (E) 2 k) =
      completePointStageNodeCubic K n h m i j k := by
  let g := (f).resLE (O) (C) (completePointStageComplement_preimage K n h m i).le
  let r := sectionRatioOn (L) (s 2) (O) le_rfl (s k)
  have h₁ := congrArg (fun z : Γ((O).toScheme, ⊤) ↦
    ((a) ∣_ (C)).appTop (g.appTop z))
      (completePointToCubicChart_coordinate K n h i 2 k)
  have h₂ := congrArg (fun z : Γ((C).toScheme, ⊤) ↦ ((a) ∣_ (C)).appTop z)
    (resLE_topIso_inv (f) (O) (C)
      (completePointStageComplement_preimage K n h m i).le r)
  have he := h₁.trans (h₂.trans
    (completePointStageNodeCubic_completeRatio K n h m i j k).symm)
  simpa only [completePointStageComplementCubicFunctions, completePointStageComplementToCubicChart,
    g, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    CommRingCat.Hom.hom, completePointLine, completePointStageNodeOpen] using he

end FLT.Mazur.PolygonInfinitesimalStages

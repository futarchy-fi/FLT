/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityWholeAction

/-!
# Original parameter charts on the whole smooth-by-polygon product

The actual rotated identity charts cover the first input while the second
input remains the entire original polygon, including every singular point.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
attribute [local instance] exactVeroneseProjToBase_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "M" => completeOriginalSmoothOver K n h
local notation "π" => exactVeroneseProjToBase K n h
local notation "C" => completeIdentityChartCover K n h (0 : Fin n)

/-- The unchanged complete polygon over its literal original coefficient base. -/
abbrev completeOriginalWholeOver : Over (Spec (.of (PowerSeries K))) := Over.mk (π)

local notation "X" => completeOriginalWholeOver K n h

/-- The original whole-input identity action as a relative morphism. -/
def completeIdentityWholeActionOver : (G).X ⊗ (X) ⟶ (X) :=
  Over.homMk (completeIdentityWholeAction K n h) (by
    change completeIdentityWholeAction K n h ≫ (π) =
      pullback.fst (G).X.hom (π) ≫ (G).X.hom
    rw [completeIdentityWholeAction_structure]
    exact pullback.condition.symm)

/-- The original smooth inclusion over the unchanged base. -/
def completeWholeSmoothInclusion : (M) ⟶ (X) :=
  Over.homMk (π).smoothLocus.ι rfl

/-- The raw cover changes only the first, smooth parameter. -/
def completeWholeActionParameterRawCover : ((M) ⊗ (X)).left.OpenCover :=
  Scheme.Pullback.openCoverOfLeft (C) (M).hom (π)

/-- Each chart is the entire original identity-action input. -/
def completeWholeActionParameterChartIso (b : ZMod n) :
    (completeWholeActionParameterRawCover K n h).X b ≅ ((G).X ⊗ (X)).left :=
  pullback.congrHom (completeIdentityChart K n h 0 b).w rfl

/-- The chart isomorphism retains the actual smooth parameter and the whole second input. -/
theorem completeWholeActionParameterChartIso_map (b : ZMod n) :
    (completeWholeActionParameterChartIso K n h b).inv ≫
      (completeWholeActionParameterRawCover K n h).f b =
        (completeIdentityChart K n h 0 b ⊗ₘ 𝟙 (X)).left := by
  dsimp only [completeOriginalWholeOver, Over.mk_hom]
  simp only [completeWholeActionParameterRawCover, Scheme.Pullback.openCoverOfLeft_f,
    completeWholeActionParameterChartIso, completeIdentityChartCover, pullback.congrHom_inv,
    Over.tensorHom_left, Over.id_left]
  apply pullback.hom_ext <;>
    simp only [Over.mk_hom, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, Category.comp_id]

/-- The constructed whole-input parameter cover uses exactly the original identity products. -/
def completeWholeActionParameterCover : ((M) ⊗ (X)).left.OpenCover :=
  (completeWholeActionParameterRawCover K n h).copy (ZMod n)
    (fun _ ↦ ((G).X ⊗ (X)).left)
    (fun b ↦ (completeIdentityChart K n h 0 b ⊗ₘ 𝟙 (X)).left) (Equiv.refl _)
    (fun b ↦ (completeWholeActionParameterChartIso K n h b).symm)
    (fun b ↦ (completeWholeActionParameterChartIso_map K n h b).symm)

end FLT.Mazur.PolygonInfinitesimalStages

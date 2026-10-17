/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteWholeActionChartCompatibility

/-!
# The full smooth group acts on the entire original polygon

The constructed rotated parameter charts agree on their actual overlaps.
Their gluing defines a polygon-valued morphism on the full relative product,
retaining every original parameter chart and the unchanged base.
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
local notation "X" => completeOriginalWholeOver K n h
local notation "C" => completeWholeActionParameterCover K n h

/-- Compatibility on any flat original scheme with identical chart inputs. -/
theorem completeWholeActionChart_common (b c : ZMod n) {T : Scheme}
    (x y : T ⟶ ((G).X ⊗ (X)).left) [Flat (x ≫ ((G).X ⊗ (X)).hom)]
    (he : x ≫ (completeIdentityChart K n h 0 b ⊗ₘ 𝟙 (X)).left =
      y ≫ (completeIdentityChart K n h 0 c ⊗ₘ 𝟙 (X)).left) :
    x ≫ (completeWholeActionChart K n h b).left =
      y ≫ (completeWholeActionChart K n h c).left := by
  have hb : y ≫ ((G).X ⊗ (X)).hom = x ≫ ((G).X ⊗ (X)).hom := by
    have hh := congrArg (· ≫ ((M) ⊗ (X)).hom) he
    simpa only [Category.assoc, Over.w] using hh.symm
  let _ : Flat (Over.mk (x ≫ ((G).X ⊗ (X)).hom)).hom :=
    inferInstanceAs (Flat (x ≫ ((G).X ⊗ (X)).hom))
  exact congrArg Over.Hom.left (completeWholeActionChart_compatible K n h b c
    (Over.homMk x rfl : Over.mk (x ≫ ((G).X ⊗ (X)).hom) ⟶ ((G).X ⊗ (X))) (Over.homMk y hb)
    (by apply Over.OverMorphism.ext; exact he))

/-- The actual parameter overlaps are flat and their whole-input actions agree. -/
theorem completeWholeActionChart_overlap (b c : ZMod n) :
    pullback.fst ((C).f b) ((C).f c) ≫ (completeWholeActionChart K n h b).left =
      pullback.snd ((C).f b) ((C).f c) ≫ (completeWholeActionChart K n h c).left := by
  let _ := completeIdentityActionParameter_flat K n h
  let _ : Flat (X).hom := exactVeroneseProjToBase_flat K n h
  let _ : Flat ((G).X ⊗ (X)).hom := completeRelative_tensor_flat K (G).X (X)
  let _ : Flat (pullback.fst ((C).f b) ((C).f c) ≫ ((G).X ⊗ (X)).hom) := by infer_instance
  exact completeWholeActionChart_common K n h b c _ _ pullback.condition

/-- The glued original polygon-valued action on the entire smooth-by-whole product. -/
def completeWholeActionMap : ((M) ⊗ (X)).left ⟶ (X).left :=
  (C).glueMorphisms (fun b ↦ (completeWholeActionChart K n h b).left)
    (completeWholeActionChart_overlap K n h)

/-- Gluing recovers every constructed whole-input parameter chart. -/
@[reassoc] theorem completeWholeActionMap_chart (b : ZMod n) :
    (completeIdentityChart K n h 0 b ⊗ₘ 𝟙 (X)).left ≫ completeWholeActionMap K n h =
      (completeWholeActionChart K n h b).left := (C).ι_glueMorphisms _ _ b

/-- The full action preserves the original power-series base. -/
@[reassoc] theorem completeWholeActionMap_base :
    completeWholeActionMap K n h ≫ (X).hom = ((M) ⊗ (X)).hom := by
  apply (C).hom_ext
  intro b
  change (completeIdentityChart K n h 0 b ⊗ₘ 𝟙 (X)).left ≫
    completeWholeActionMap K n h ≫ (X).hom =
    (completeIdentityChart K n h 0 b ⊗ₘ 𝟙 (X)).left ≫ _
  rw [completeWholeActionMap_chart_assoc]
  exact (completeWholeActionChart K n h b).w.trans
    (completeIdentityChart K n h 0 b ⊗ₘ 𝟙 (X)).w.symm

/-- The constructed full action as a morphism over the unchanged original base. -/
def completeWholeAction : (M) ⊗ (X) ⟶ (X) :=
  Over.homMk (completeWholeActionMap K n h) (completeWholeActionMap_base K n h)

/-- Every original parameter chart acts by its constructed polygon-valued formula. -/
@[reassoc] theorem completeWholeAction_chart (b : ZMod n) :
    (completeIdentityChart K n h 0 b ⊗ₘ 𝟙 (X)) ≫ completeWholeAction K n h =
      completeWholeActionChart K n h b := by
  apply Over.OverMorphism.ext
  exact completeWholeActionMap_chart K n h b

end FLT.Mazur.PolygonInfinitesimalStages

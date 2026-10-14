/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteChartOperationCompatibility

/-!
# Inversion on the entire original smooth complete polygon

The proved chart compatibility glues the actual identity-group inverse
and negative-label rotations. The resulting global morphism is over the
unchanged base and is an involution on the full smooth scheme.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj GrpObj
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
attribute [local instance] exactVeroneseProjToBase_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "M" => completeOriginalSmoothOver K n h
local notation "C" => completeIdentityChartCover K n h (0 : Fin n)

/-- Scheme-level compatibility of inversion on any two chart presentations. -/
theorem completeChartInv_common (b c : ZMod n) {T : Scheme}
    (x y : T ⟶ (G).X.left)
    (he : x ≫ (completeIdentityChart K n h 0 b).left =
      y ≫ (completeIdentityChart K n h 0 c).left) :
    x ≫ (completeIdentityChartInv K n h 0 b).left =
      y ≫ (completeIdentityChartInv K n h 0 c).left := by
  have hb : y ≫ (G).X.hom = x ≫ (G).X.hom := by
    calc
      _ = (y ≫ (completeIdentityChart K n h 0 c).left) ≫ (M).hom := by
        rw [Category.assoc, (completeIdentityChart K n h 0 c).w]
      _ = (x ≫ (completeIdentityChart K n h 0 b).left) ≫ (M).hom :=
        congrArg (· ≫ (M).hom) he.symm
      _ = _ := by rw [Category.assoc, (completeIdentityChart K n h 0 b).w]
  exact congrArg Over.Hom.left (completeChartInv_compatible K n h b c
    (Over.homMk x (by rfl) : Over.mk (x ≫ (G).X.hom) ⟶ (G).X)
    (Over.homMk y hb) (by apply Over.OverMorphism.ext; exact he))

/-- The glued scheme map on the whole original smooth locus. -/
def completeSmoothInvMap : (M).left ⟶ (M).left :=
  (C).glueMorphisms (fun b ↦ (completeIdentityChartInv K n h 0 b).left)
    (fun b c ↦ completeChartInv_common K n h b c _ _ pullback.condition)

/-- Global inversion restricts to the actual original inverse in each negative-label chart. -/
@[reassoc] theorem completeSmoothInvMap_chart (b : ZMod n) :
    (completeIdentityChart K n h 0 b).left ≫ completeSmoothInvMap K n h =
      (completeIdentityChartInv K n h 0 b).left :=
  (C).ι_glueMorphisms _ _ b

/-- The glued inversion retains the original structural morphism. -/
@[reassoc] theorem completeSmoothInvMap_base :
    completeSmoothInvMap K n h ≫ (M).hom = (M).hom := by
  apply (C).hom_ext
  intro b
  change ZMod n at b
  change (completeIdentityChart K n h 0 b).left ≫ completeSmoothInvMap K n h ≫
    (M).hom = (completeIdentityChart K n h 0 b).left ≫ (M).hom
  rw [completeSmoothInvMap_chart_assoc]
  exact (completeIdentityChartInv K n h 0 b).w.trans
    (completeIdentityChart K n h 0 b).w.symm

/-- Inversion as a morphism over the unchanged original power-series base. -/
def completeSmoothInv : (M) ⟶ (M) :=
  Over.homMk (completeSmoothInvMap K n h) (completeSmoothInvMap_base K n h)

/-- The global inverse retains every original chart formula over the base. -/
@[reassoc] theorem completeSmoothInv_chart (b : ZMod n) :
    completeIdentityChart K n h 0 b ≫ completeSmoothInv K n h =
      completeIdentityChartInv K n h 0 b := by
  apply Over.OverMorphism.ext
  exact completeSmoothInvMap_chart K n h b

/-- Inverting twice is the identity on the entire original smooth scheme. -/
theorem completeSmoothInv_involutive :
    completeSmoothInv K n h ≫ completeSmoothInv K n h = 𝟙 (M) := by
  have hi : (ι[(G).X]).left ≫ (ι[(G).X]).left = 𝟙 (G).X.left := by
    have he : ι[(G).X] ≫ ι[(G).X] = 𝟙 (G).X := by
      simpa only [Hom.inv_def, Category.id_comp] using inv_inv (𝟙 (G).X)
    exact congrArg Over.Hom.left he
  apply Over.OverMorphism.ext
  apply (C).hom_ext
  intro b
  change ZMod n at b
  change (completeIdentityChart K n h 0 b).left ≫
    completeSmoothInvMap K n h ≫ completeSmoothInvMap K n h =
      (completeIdentityChart K n h 0 b).left ≫ 𝟙 _
  rw [completeSmoothInvMap_chart_assoc]
  change ((ι[(G).X]).left ≫ (completeIdentityChart K n h 0 (-b)).left) ≫
    completeSmoothInvMap K n h = _
  rw [Category.assoc, completeSmoothInvMap_chart]
  change (ι[(G).X]).left ≫ (ι[(G).X]).left ≫
    (completeIdentityChart K n h 0 (- -b)).left = _
  rw [← Category.assoc, hi, Category.id_comp, neg_neg, Category.comp_id]

end FLT.Mazur.PolygonInfinitesimalStages

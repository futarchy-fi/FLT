/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothProductCover

/-!
# Multiplication on the entire original smooth polygon

The original chart products agree on every overlap, hence glue to an
actual morphism on the full smooth relative product over the original base.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj GrpObj
open CartesianMonoidalCategory
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

/-- Compatibility on arbitrary relative test objects for pairs of chart coordinates. -/
theorem completeChartMul_pair_compatible {T : Over (Spec (.of (PowerSeries K)))}
    (b c d e : ZMod n) (x y : T ⟶ (G).X ⊗ (G).X)
    (he : x ≫ (completeIdentityChart K n h 0 b ⊗ₘ completeIdentityChart K n h 0 c) =
      y ≫ (completeIdentityChart K n h 0 d ⊗ₘ completeIdentityChart K n h 0 e)) :
    x ≫ completeIdentityChartMul K n h 0 b c =
      y ≫ completeIdentityChartMul K n h 0 d e := by
  have hx := congrArg (· ≫ fst (M) (M)) he
  have hy := congrArg (· ≫ snd (M) (M)) he
  simp only [Category.assoc, tensorHom_fst, tensorHom_snd] at hx hy
  have hm := completeChartMul_compatible K n h b c d e
    (x ≫ fst _ _) (y ≫ fst _ _) (x ≫ snd _ _) (y ≫ snd _ _) hx hy
  simpa only [← comp_lift, lift_fst_snd, Category.comp_id] using hm

/-- Scheme-level compatibility needed by the actual product open-cover gluing. -/
theorem completeChartMul_pair_common (b c d e : ZMod n) {T : Scheme}
    (x y : T ⟶ ((G).X ⊗ (G).X).left)
    (he : x ≫ (completeIdentityChart K n h 0 b ⊗ₘ
        completeIdentityChart K n h 0 c).left =
      y ≫ (completeIdentityChart K n h 0 d ⊗ₘ
        completeIdentityChart K n h 0 e).left) :
    x ≫ (completeIdentityChartMul K n h 0 b c).left =
      y ≫ (completeIdentityChartMul K n h 0 d e).left := by
  have hb : y ≫ ((G).X ⊗ (G).X).hom = x ≫ ((G).X ⊗ (G).X).hom := by
    calc
      _ = (y ≫ (completeIdentityChart K n h 0 d ⊗ₘ
          completeIdentityChart K n h 0 e).left) ≫ ((M) ⊗ (M)).hom := by
        rw [Category.assoc, (completeIdentityChart K n h 0 d ⊗ₘ
          completeIdentityChart K n h 0 e).w]
      _ = (x ≫ (completeIdentityChart K n h 0 b ⊗ₘ
          completeIdentityChart K n h 0 c).left) ≫ ((M) ⊗ (M)).hom :=
        congrArg (· ≫ ((M) ⊗ (M)).hom) he.symm
      _ = _ := by rw [Category.assoc, (completeIdentityChart K n h 0 b ⊗ₘ
          completeIdentityChart K n h 0 c).w]
  exact congrArg Over.Hom.left (completeChartMul_pair_compatible K n h b c d e
    (Over.homMk x (by rfl) : Over.mk (x ≫ ((G).X ⊗ (G).X).hom) ⟶ (G).X ⊗ (G).X)
    (Over.homMk y hb) (by apply Over.OverMorphism.ext; exact he))

/-- Multiplication glued on the entire original smooth product. -/
def completeSmoothMulMap : ((M) ⊗ (M)).left ⟶ (M).left :=
  (completeSmoothProductCover K n h).glueMorphisms
    (fun p ↦ (completeIdentityChartMul K n h 0 p.1 p.2).left)
    (fun p q ↦ completeChartMul_pair_common K n h p.1 p.2 q.1 q.2 _ _ pullback.condition)

/-- The glued multiplication retains the full original local chart formula. -/
@[reassoc] theorem completeSmoothMulMap_chart (b c : ZMod n) :
    (completeIdentityChart K n h 0 b ⊗ₘ completeIdentityChart K n h 0 c).left ≫
        completeSmoothMulMap K n h = (completeIdentityChartMul K n h 0 b c).left :=
  (completeSmoothProductCover K n h).ι_glueMorphisms _ _ (b, c)

/-- The glued product is over the unchanged original base. -/
@[reassoc] theorem completeSmoothMulMap_base :
    completeSmoothMulMap K n h ≫ (M).hom = ((M) ⊗ (M)).hom := by
  apply (completeSmoothProductCover K n h).hom_ext
  rintro ⟨b, c⟩
  change (completeIdentityChart K n h 0 b ⊗ₘ completeIdentityChart K n h 0 c).left ≫
    completeSmoothMulMap K n h ≫ (M).hom =
    (completeIdentityChart K n h 0 b ⊗ₘ completeIdentityChart K n h 0 c).left ≫ _
  rw [completeSmoothMulMap_chart_assoc]
  exact (completeIdentityChartMul K n h 0 b c).w.trans
    (completeIdentityChart K n h 0 b ⊗ₘ completeIdentityChart K n h 0 c).w.symm

/-- Multiplication as an actual relative scheme morphism. -/
def completeSmoothMul : (M) ⊗ (M) ⟶ (M) :=
  Over.homMk (completeSmoothMulMap K n h) (completeSmoothMulMap_base K n h)

/-- Every pair of original charts satisfies its constructed relative multiplication formula. -/
@[reassoc] theorem completeSmoothMul_chart (b c : ZMod n) :
    (completeIdentityChart K n h 0 b ⊗ₘ completeIdentityChart K n h 0 c) ≫
      completeSmoothMul K n h = completeIdentityChartMul K n h 0 b c := by
  apply Over.OverMorphism.ext
  exact completeSmoothMulMap_chart K n h b c

end FLT.Mazur.PolygonInfinitesimalStages

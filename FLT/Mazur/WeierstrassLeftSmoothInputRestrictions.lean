/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothYAddition
public import FLT.Mazur.WeierstrassLeftSmoothMixedAddition

/-!
# Formulas retained by the enlarged projective chart laws

The pullback universal property recovers the affine, polynomial and infinity
formulas on every scheme with the prescribed original input pair.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The mixed law retains the enlarged affine formula on arbitrary common inputs. -/
theorem leftSmoothMixedAddition_affine (b c : Bool) (ha : b = false ∨ c = false)
    {X : Scheme.{u}} (f : X ⟶ (leftSmoothProductChartOpen W b c).toScheme)
    (g : X ⟶ (leftSmoothAffineOverlapOpen W b c).toScheme)
    (h : f ≫ (leftSmoothProductChartOpen W b c).ι =
      g ≫ leftSmoothAffineOverlapInput W b c) :
    f ≫ leftSmoothMixedAddition W b c ha = g ≫ leftSmoothAffineOverlapAddition W b c := by
  let l : X ⟶ (leftSmoothMixedCover W b c ha).X true :=
    pullback.lift f (g ≫ (leftSmoothAffineOverlapOpen W b c).ι) (by
      change f ≫ (leftSmoothProductChartOpen W b c).ι =
        (g ≫ (leftSmoothAffineOverlapOpen W b c).ι) ≫
          integralProductOverlapFst W b c false false
      rw [Category.assoc]
      exact h)
  have hl : l ≫ (leftSmoothMixedCover W b c ha).f true = f := pullback.lift_fst _ _ _
  have hg : l ≫ leftSmoothMixedAffineLift W b c ha = g := by
    apply (cancel_mono (leftSmoothAffineOverlapOpen W b c).ι).mp
    rw [Category.assoc, leftSmoothMixedAffineLift_inclusion]
    exact pullback.lift_snd _ _ _
  rw [← hl, Category.assoc, leftSmoothMixedLocal_glued]
  change l ≫ (leftSmoothMixedAffineLift W b c ha ≫ _) = _
  rw [← Category.assoc, hg]

/-- The mixed law retains the actual polynomial output-Z formula. -/
theorem leftSmoothMixedAddition_polynomial (b c : Bool) (ha : b = false ∨ c = false)
    {X : Scheme.{u}} (f : X ⟶ (leftSmoothProductChartOpen W b c).toScheme)
    (g : X ⟶ Spec (.of (AdditionOutputOpen W
      (productChartCoordinate b) (productChartCoordinate c) 2)))
    (h : f ≫ (leftSmoothProductChartOpen W b c).ι = g ≫
      projectiveAdditionInclusion W (productChartCoordinate b) (productChartCoordinate c) 2) :
    f ≫ leftSmoothMixedAddition W b c ha =
      g ≫ Spec.map (CommRingCat.ofHom (projectiveAdditionChart W
        (productChartCoordinate b) (productChartCoordinate c) 2).toRingHom) ≫
          integralCurveChart W 2 := by
  let l : X ⟶ (leftSmoothMixedCover W b c ha).X false := pullback.lift f g h
  have hl : l ≫ (leftSmoothMixedCover W b c ha).f false = f := pullback.lift_fst _ _ _
  have hg : l ≫ leftSmoothMixedProjection W b c ha false = g := pullback.lift_snd _ _ _
  rw [← hl, Category.assoc, leftSmoothMixedLocal_glued]
  change l ≫ (leftSmoothMixedProjection W b c ha false ≫ _) = _
  rw [← Category.assoc, hg]

/-- The Y/Y law retains the enlarged affine formula on arbitrary common inputs. -/
theorem leftSmoothYAddition_affine {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothProductChartOpen W true true).toScheme)
    (g : X ⟶ (leftSmoothAffineOverlapOpen W true true).toScheme)
    (h : f ≫ (leftSmoothProductChartOpen W true true).ι =
      g ≫ leftSmoothAffineOverlapInput W true true) :
    f ≫ leftSmoothYAddition W = g ≫ leftSmoothAffineOverlapAddition W true true := by
  let l : X ⟶ (leftSmoothYCover W).X .affine :=
    pullback.lift f (g ≫ (leftSmoothAffineOverlapOpen W true true).ι) (by
      change f ≫ (leftSmoothProductChartOpen W true true).ι =
        (g ≫ (leftSmoothAffineOverlapOpen W true true).ι) ≫
          integralProductOverlapFst W true true false false
      rw [Category.assoc]
      exact h)
  have hl : l ≫ (leftSmoothYCover W).f .affine = f := pullback.lift_fst _ _ _
  have hg : l ≫ leftSmoothYAffineLift W = g := by
    apply (cancel_mono (leftSmoothAffineOverlapOpen W true true).ι).mp
    rw [Category.assoc, leftSmoothYAffineLift_inclusion]
    exact pullback.lift_snd _ _ _
  rw [← hl, Category.assoc, leftSmoothYLocal_glued]
  change l ≫ (leftSmoothYAffineLift W ≫ _) = _
  rw [← Category.assoc, hg]

/-- The Y/Y law retains the actual polynomial output-Z formula. -/
theorem leftSmoothYAddition_polynomial {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothProductChartOpen W true true).toScheme)
    (g : X ⟶ Spec (.of (AdditionOutputOpen W 1 1 2)))
    (h : f ≫ (leftSmoothProductChartOpen W true true).ι =
      g ≫ projectiveAdditionInclusion W 1 1 2) :
    f ≫ leftSmoothYAddition W = g ≫
      Spec.map (CommRingCat.ofHom (projectiveAdditionChart W 1 1 2).toRingHom) ≫
        integralCurveChart W 2 := by
  let l : X ⟶ (leftSmoothYCover W).X .polynomial := pullback.lift f g h
  have hl : l ≫ (leftSmoothYCover W).f .polynomial = f := pullback.lift_fst _ _ _
  have hg : l ≫ leftSmoothYProjection W .polynomial = g := pullback.lift_snd _ _ _
  rw [← hl, Category.assoc, leftSmoothYLocal_glued]
  change l ≫ (leftSmoothYProjection W .polynomial ≫ _) = _
  rw [← Category.assoc, hg]

/-- The Y/Y law retains its actual regular infinity formula. -/
theorem leftSmoothYAddition_infinity {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothProductChartOpen W true true).toScheme)
    (g : X ⟶ Spec (.of (InfinityAdditionOpen W)))
    (h : f ≫ (leftSmoothProductChartOpen W true true).ι = g ≫ infinityAdditionInclusion W) :
    f ≫ leftSmoothYAddition W = g ≫ infinityAdditionSpec W ≫ integralCurveChart W 1 := by
  let l : X ⟶ (leftSmoothYCover W).X .infinity := pullback.lift f g h
  have hl : l ≫ (leftSmoothYCover W).f .infinity = f := pullback.lift_fst _ _ _
  have hg : l ≫ leftSmoothYProjection W .infinity = g := pullback.lift_snd _ _ _
  rw [← hl, Category.assoc, leftSmoothYLocal_glued]
  change l ≫ (leftSmoothYProjection W .infinity ≫ _) = _
  rw [← Category.assoc, hg]

end FLT.Mazur.WeierstrassIntegralChart

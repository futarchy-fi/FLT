/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluSmoothPointComparison

/-!
# Coordinates and scalar extension of original smooth points

The smooth point of an original affine point retains its normalized chart
coordinates. Scalar extension is precomposition by the original spectrum map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K L : Type} [Field K] [Field L] [Algebra K L] (E : WeierstrassCurve K)

/-- The smooth comparison retains the original affine coordinates. -/
@[reassoc] theorem affineSmoothPoint_some {x y : L}
    (h : (E.map (algebraMap K L)).toAffine.Nonsingular x y) :
    affineSmoothPoint E (.some x y h) ≫ (integralSmoothOpen E).ι =
      integralChartPoint E 2 ![x, y, 1] ((Projective.equation_some x y).mpr h.1) rfl := by
  rw [affineSmoothPoint, projectiveToSmooth_inclusion]
  exact projectiveToIntegral_chart E _ 2 ![x, y, 1]
    ((Projective.equation_some x y).mpr h.1) rfl rfl

/-- The zero affine point is the original infinity section. -/
@[reassoc] theorem affineSmoothPoint_zero :
    affineSmoothPoint E (0 : (E.map (algebraMap K L)).toAffine.Point) ≫
        (integralSmoothOpen E).ι =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ integralCurveZero E := by
  rw [affineSmoothPoint, projectiveToSmooth_inclusion]
  exact projectiveToIntegral_zero E

variable [DecidableEq K] [DecidableEq L]

/-- Scalar extension of the original affine point retains the actual smooth scheme point. -/
theorem affineSmoothPoint_base (P : E.toAffine.Point) :
    Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ affineSmoothPoint E P =
      affineSmoothPoint E (Affine.Point.map (W' := E.toAffine) (Algebra.ofId K L) P) := by
  apply (cancel_mono (integralSmoothOpen E).ι).mp
  rw [Category.assoc]
  cases P with
  | zero =>
    change Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
      affineSmoothPoint E (0 : (E.map (algebraMap K K)).toAffine.Point) ≫
        (integralSmoothOpen E).ι =
      affineSmoothPoint E (0 : (E.map (algebraMap K L)).toAffine.Point) ≫
        (integralSmoothOpen E).ι
    rw [affineSmoothPoint_zero, affineSmoothPoint_zero]
    change _ ≫ Spec.map (𝟙 (CommRingCat.of K)) ≫ _ = _
    rw [Spec.map_id, Category.id_comp]
  | some x y h =>
    rw [Affine.Point.map_some, affineSmoothPoint_some, affineSmoothPoint_some,
      integralChartPoint, integralChartPoint, ← Spec.map_comp_assoc]
    congr 2
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change ((Algebra.ofId K L).comp
      (evaluation E 2 ![x, y, 1]
        ((Projective.equation_some x y).mpr h.1) rfl)) a =
      evaluation E 2 _ ((Projective.equation_some _ _).mpr
        ((Affine.map_nonsingular E.toAffine (algebraMap K L).injective x y).mpr h).1) rfl a
    congr 1
    apply hom_ext
    intro i
    simp only [AlgHom.comp_apply, evaluation_coord]
    fin_cases i <;> simp

end WeierstrassCurve.Velu

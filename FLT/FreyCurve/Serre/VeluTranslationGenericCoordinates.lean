/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluAffineTranslation
public import FLT.FreyCurve.Serre.VeluSourceChart
public import FLT.FreyCurve.Serre.VeluTranslation

/-!
# Generic coordinates of the actual source translation

The existing whole-cubic translation sends the actual source generic point to
the original chord coordinates `translateX` and `translateY`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- The actual generic source point in the original affine point group. -/
def sourceGenericAffinePoint : (E.map (algebraMap K (FunctionField E))).toAffine.Point :=
  .some (genericX E) (genericY E) (Affine.equation_iff_nonsingular.mp (generic_equation E))

/-- Its smooth scheme point is exactly the original source chart evaluation. -/
@[reassoc] theorem sourceGenericAffinePoint_inclusion :
    affineSmoothPoint E (sourceGenericAffinePoint E) ≫ (integralSmoothOpen E).ι =
      Spec.map (CommRingCat.ofHom (sourceGenericChart E).toRingHom) ≫
        integralCurveChart E 2 := by
  rw [sourceGenericAffinePoint, affineSmoothPoint_some]
  rfl

variable [DecidableEq K]

/-- Classical translation of the original generic point has the original chord coordinates. -/
theorem sourceGenericAffinePoint_add [DecidableEq (FunctionField E)]
    {u v : K} (hQ : E.toAffine.Nonsingular u v) :
    affineScalarPoint E (.some u v hQ) +
        sourceGenericAffinePoint E =
      .some (translateX E u v) (translateY E u v) (translate_nonsingular E hQ) := by
  classical
  rw [add_comm]
  change Affine.Point.some (genericX E) (genericY E)
      (Affine.equation_iff_nonsingular.mp (generic_equation E)) +
    Affine.Point.some (algebraMap K _ u) (algebraMap K _ v)
      ((Affine.map_nonsingular E.toAffine
        (algebraMap K (FunctionField E)).injective u v).mpr hQ) = _
  rw [Affine.Point.add_of_X_ne (genericX_ne_constant E u)]
  simp only [Affine.slope_of_X_ne (genericX_ne_constant E u), translateX, translateY]

omit [DecidableEq K] in
/-- The actual generic image under translation evaluates the original chord formulas. -/
@[reassoc] theorem affineTranslationIso_generic {u v : K}
    (hQ : E.toAffine.Nonsingular u v) :
    (Spec.map (CommRingCat.ofHom (sourceGenericChart E).toRingHom) ≫
        integralCurveChart E 2) ≫ (affineTranslationIso E (.some u v hQ)).hom =
      integralChartPoint E 2 ![translateX E u v, translateY E u v, 1]
        ((Projective.equation_some _ _).mpr (translate_nonsingular E hQ).1) rfl := by
  classical
  rw [← sourceGenericAffinePoint_inclusion, affineTranslationIso_action,
    sourceGenericAffinePoint_add, affineSmoothPoint_some]

end WeierstrassCurve.Velu

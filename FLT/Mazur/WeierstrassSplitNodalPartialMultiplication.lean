/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalPointBaseChange
public import FLT.Mazur.WeierstrassPartialFieldPointComparison

/-!
# Nodal partial addition is unit multiplication over every field algebra

For field-valued points, all four original addition chart morphisms,
and hence the actual partial addition, output the product of the two Laurent
units. The comparison is an equality of maps from the field spectrum into
the original glued cubic, with no good-reduction assumption.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K] (a : Rˣ)

/-- Every classical sum has the actual torus scheme point with the product Laurent parameter. -/
theorem splitNodal_relative_projective_sum_toIntegral
    (P Q : ((splitNodalEquation a).map (algebraMap R K)).toProjective.Point) :
    (projectiveToIntegral (splitNodalEquation a) (P + Q)).left =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R)
        ((splitNodalUnitPointEquiv a).symm P * (splitNodalUnitPointEquiv a).symm Q)).toRingHom) ≫
          splitNodalTorusToCurve a := by
  have h := splitNodalUnitPoint_toIntegral a ((splitNodalUnitPointEquiv a).symm (P + Q))
  rw [Equiv.apply_symm_apply, splitNodalUnitPoint_relative_symm_add] at h
  exact h

variable (i : AdditionChartIndex)
  (f : additionChartRing (splitNodalEquation a) i →ₐ[R] K)
  (h₁ : ((splitNodalEquation a).map (algebraMap R K)).toAffine.Nonsingular
    (f (additionInputLeft (splitNodalEquation a) i (coord (splitNodalEquation a) 2 0)))
    (f (additionInputLeft (splitNodalEquation a) i (coord (splitNodalEquation a) 2 1))))
  (h₂ : ((splitNodalEquation a).map (algebraMap R K)).toAffine.Nonsingular
    (f (additionInputRight (splitNodalEquation a) i (coord (splitNodalEquation a) 2 0)))
    (f (additionInputRight (splitNodalEquation a) i (coord (splitNodalEquation a) 2 1))))

/-- On all four addition charts, the original cubic-valued output is unit multiplication. -/
theorem splitNodal_additionFieldPoint_multiplication :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        additionCurveChart (splitNodalEquation a) i =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R)
        ((splitNodalUnitPointEquiv a).symm (Point.fromAffine (.some _ _ h₁)) *
          (splitNodalUnitPointEquiv a).symm (Point.fromAffine (.some _ _ h₂)))).toRingHom) ≫
        splitNodalTorusToCurve a :=
  (additionFieldPoint_chart_sum (splitNodalEquation a) i f h₁ h₂).trans
    (splitNodal_relative_projective_sum_toIntegral a _ _)

/-- The actual partial addition agrees with unit multiplication on field-valued inputs. -/
theorem splitNodal_partialFieldPoint_multiplication :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        additionChartToDomain (splitNodalEquation a) i ≫
          affinePartialAddition (splitNodalEquation a) =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R)
        ((splitNodalUnitPointEquiv a).symm (Point.fromAffine (.some _ _ h₁)) *
          (splitNodalUnitPointEquiv a).symm (Point.fromAffine (.some _ _ h₂)))).toRingHom) ≫
        splitNodalTorusToCurve a := by
  rw [additionChartToDomain_addition]
  exact splitNodal_additionFieldPoint_multiplication a i f h₁ h₂

end FLT.Mazur.WeierstrassIntegralChart

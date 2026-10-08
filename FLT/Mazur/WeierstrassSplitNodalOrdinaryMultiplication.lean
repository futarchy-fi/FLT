/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalPointMultiplication
public import FLT.Mazur.WeierstrassPartialOrdinaryPointComparison

/-!
# Comparing nodal multiplication with the actual ordinary addition charts

For field-valued points, the original secant and tangent chart morphisms,
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
variable {K : Type u} [Field K] (a : Kˣ)

/-- Every classical sum has the actual torus scheme point with the product Laurent parameter. -/
theorem splitNodal_projective_sum_toIntegral
    (P Q : ((splitNodalEquation a).map (algebraMap K K)).toProjective.Point) :
    (projectiveToIntegral (splitNodalEquation a) (P + Q)).left =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := K)
        ((splitNodalUnitPointEquiv a).symm P * (splitNodalUnitPointEquiv a).symm Q)).toRingHom) ≫
          splitNodalTorusToCurve a := by
  have h := splitNodalUnitPoint_toIntegral a ((splitNodalUnitPointEquiv a).symm (P + Q))
  rw [Equiv.apply_symm_apply, splitNodalUnitPoint_symm_add] at h
  exact h

variable (b : Bool)
  (f : additionChartRing (splitNodalEquation a) (ordinaryIndex b) →ₐ[K] K)
  (h₁ : ((splitNodalEquation a).map (algebraMap K K)).toAffine.Nonsingular
    (f (ordinaryInputLeft (splitNodalEquation a) b (coord (splitNodalEquation a) 2 0)))
    (f (ordinaryInputLeft (splitNodalEquation a) b (coord (splitNodalEquation a) 2 1))))
  (h₂ : ((splitNodalEquation a).map (algebraMap K K)).toAffine.Nonsingular
    (f (ordinaryInputRight (splitNodalEquation a) b (coord (splitNodalEquation a) 2 0)))
    (f (ordinaryInputRight (splitNodalEquation a) b (coord (splitNodalEquation a) 2 1))))

/-- On both ordinary charts, the original cubic-valued output is unit multiplication. -/
theorem splitNodal_ordinaryFieldPoint_multiplication :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        additionCurveChart (splitNodalEquation a) (ordinaryIndex b) =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := K)
        ((splitNodalUnitPointEquiv a).symm (Point.fromAffine (.some _ _ h₁)) *
          (splitNodalUnitPointEquiv a).symm (Point.fromAffine (.some _ _ h₂)))).toRingHom) ≫
        splitNodalTorusToCurve a :=
  (ordinaryFieldPoint_chart_sum (splitNodalEquation a) b f h₁ h₂).trans
    (splitNodal_projective_sum_toIntegral a _ _)

/-- The actual partial addition agrees with unit multiplication on ordinary field-valued inputs. -/
theorem splitNodal_partialOrdinaryFieldPoint_multiplication :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        additionChartToDomain (splitNodalEquation a) (ordinaryIndex b) ≫
          affinePartialAddition (splitNodalEquation a) =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := K)
        ((splitNodalUnitPointEquiv a).symm (Point.fromAffine (.some _ _ h₁)) *
          (splitNodalUnitPointEquiv a).symm (Point.fromAffine (.some _ _ h₂)))).toRingHom) ≫
        splitNodalTorusToCurve a := by
  rw [additionChartToDomain_addition]
  exact splitNodal_ordinaryFieldPoint_multiplication a b f h₁ h₂

end FLT.Mazur.WeierstrassIntegralChart

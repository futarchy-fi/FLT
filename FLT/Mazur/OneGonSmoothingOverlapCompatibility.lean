/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingOverlapCoordinates

/-!
# Compatibility on the original one-gon overlap

The original Möbius transition and the cubic's homogeneous normalization give
the same morphism, so the two original charts map consistently to the cubic.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart PolygonNodePresentation OneGonTransition
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K]

/-- The actual Laurent overlap restriction preserves the coefficient algebra. -/
def torusPunctureAlgebraMap : K[T;T⁻¹] →ₐ[K] puncture K where
  __ := overlapMap K
  commutes' r := overlapMap_C K r

/-- The two infinity-chart restrictions are the same original coordinate map. -/
theorem zeroOverlap_transitionBase :
    (zeroOverlapPuncture K).comp (transitionBase (equation (0 : K)) 2 1) =
      (torusPunctureAlgebraMap K).comp zeroInfinityToTorus := by
  apply hom_ext
  intro i
  fin_cases i
  · change zeroOverlapPuncture K (transitionBase (equation (0 : K)) 2 1
      (coord (equation (0 : K)) 1 0)) =
        torusPunctureAlgebraMap K (zeroInfinityToTorus (coord (equation (0 : K)) 1 0))
    rw [transitionBase_coord, map_mul, zeroOverlapPuncture_inverse,
      zeroOverlapPuncture_coord, zeroAffinePuncture_x, zeroInfinityToTorus_x,
      map_sub, map_one]
    change _ = 1 - overlapMap K (LaurentPolynomial.T (-1))
    rw [overlapMap_T_neg, one_sub_mobius_inverse]
    change (↑((coordinate K ^ 2 * difference K)⁻¹ * (coordinate K * difference K)) :
      puncture K) = ↑(coordinate K)⁻¹
    congr 1
    simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]
  · simp [coord_self]
  · change zeroOverlapPuncture K (transitionBase (equation (0 : K)) 2 1
      (coord (equation (0 : K)) 1 2)) =
        torusPunctureAlgebraMap K (zeroInfinityToTorus (coord (equation (0 : K)) 1 2))
    rw [transitionBase_coord, overlapCoord_self, mul_one, zeroOverlapPuncture_inverse,
      zeroInfinityToTorus_z, map_mul, map_pow, map_sub, map_one]
    change _ = overlapMap K (LaurentPolynomial.T 1) *
      (1 - overlapMap K (LaurentPolynomial.T (-1))) ^ 3
    rw [overlapMap_T, overlapMap_T_neg, one_sub_mobius_inverse]
    change (↑((coordinate K ^ 2 * difference K)⁻¹) : puncture K) =
      ↑(mobius K * ((coordinate K)⁻¹) ^ 3)
    congr 1
    dsimp [mobius]
    simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]

/-- The original puncture maps into the actual Y/Z chart intersection. -/
def zeroPunctureToOverlap : Spec (.of (puncture K)) ⟶
    overlapScheme (equation (0 : K)) 2 1 :=
  Spec.map (CommRingCat.ofHom (zeroOverlapPuncture K).toRingHom)

/-- The overlap map retains the original pinched-chart restriction. -/
@[reassoc] theorem zeroPunctureToOverlap_affine :
    zeroPunctureToOverlap K ≫ overlapInclusion (equation (0 : K)) 2 1 =
      bPuncture K ≫ (zeroNodeChartIso K).hom := by
  have h : (zeroOverlapPuncture K).comp
      (overlapRestriction (equation (0 : K)) 2 1) = zeroAffinePuncture K := by
    apply hom_ext
    intro i
    exact zeroOverlapPuncture_coord K i
  have hs := congrArg (fun f : Coordinate (equation (0 : K)) 2 →ₐ[K] puncture K =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) h
  change Spec.map (CommRingCat.ofHom (zeroOverlapPuncture K).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (overlapRestriction (equation (0 : K)) 2 1).toRingHom) =
    Spec.map (CommRingCat.ofHom (nodePunctureAlgebraMap K).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (zeroAffineNodeEquiv K).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact hs

/-- The other overlap projection retains the original Möbius transition. -/
@[reassoc] theorem zeroPunctureToOverlap_infinity :
    zeroPunctureToOverlap K ≫
        Spec.map (CommRingCat.ofHom (transitionBase (equation (0 : K)) 2 1).toRingHom) =
      toTorus K ≫ (zeroTorusChartIso K).hom := by
  rw [toTorus_eq_specMap]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (zeroOverlap_transitionBase K)

/-- The original gluing overlap is respected in the entire cubic. -/
@[reassoc] theorem zeroChart_compatibility :
    bPuncture K ≫ zeroNodeInclusion K = toTorus K ≫ zeroTorusInclusion K := by
  simpa only [zeroNodeInclusion, zeroTorusInclusion, Category.assoc] using
    integralCurve_output_eq (equation (0 : K)) 2 1
      (bPuncture K ≫ (zeroNodeChartIso K).hom)
      (toTorus K ≫ (zeroTorusChartIso K).hom) (zeroPunctureToOverlap K)
      (zeroPunctureToOverlap_affine K) (zeroPunctureToOverlap_infinity K)

end FLT.Mazur.OneGonSmoothing

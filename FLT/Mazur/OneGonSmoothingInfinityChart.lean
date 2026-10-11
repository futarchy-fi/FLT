/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingInfinityCoordinates
public import FLT.Mazur.OneGonGluing
public import FLT.Mazur.WeierstrassIntegralCurveMorphisms

/-!
# The infinity chart is the original one-gon torus

The inverse polynomial from the chart relation proves that the two coordinate
maps are inverse, with no field or characteristic restriction on the algebra.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R]

/-- The composite fixes the actual infinity chart. -/
theorem torusToZeroInfinity_comp :
    torusToZeroInfinity.comp (zeroInfinityToTorus (R := R)) = AlgHom.id R _ := by
  apply hom_ext
  intro i
  fin_cases i
  · simp
  · simp [coord_self]
  · change torusToZeroInfinity (zeroInfinityToTorus
      (coord (equation (0 : R)) 1 2)) = coord (equation (0 : R)) 1 2
    simp only [zeroInfinityToTorus_z, map_mul, map_pow, map_sub,
      map_one, torusToZeroInfinity_T, torusToZeroInfinity_T_neg, sub_sub_cancel]
    have h := zeroInfinity_relation (R := R)
    have hi := (zeroInfinityParameter (R := R)).val_inv
    change (1 + coord (equation (0 : R)) 1 0 + coord (equation (0 : R)) 1 0 ^ 2 +
      coord (equation (0 : R)) 1 2) * (1 - coord (equation (0 : R)) 1 0) = 1 at hi
    linear_combination
      -(1 + coord (equation (0 : R)) 1 0 + coord (equation (0 : R)) 1 0 ^ 2 +
        coord (equation (0 : R)) 1 2) * h + coord (equation (0 : R)) 1 2 * hi

/-- The composite also fixes the two Laurent generators. -/
theorem zeroInfinityToTorus_comp :
    (zeroInfinityToTorus (R := R)).comp torusToZeroInfinity = AlgHom.id R _ := by
  apply LaurentUnitPoints.hom_ext
  · simp only [AlgHom.comp_apply, torusToZeroInfinity_T, map_add, map_one,
      zeroInfinityToTorus_x, map_pow, zeroInfinityToTorus_z, AlgHom.id_apply]
    have ht : (LaurentPolynomial.T 1 : R[T;T⁻¹]) * LaurentPolynomial.T (-1) = 1 := by
      rw [← LaurentPolynomial.T_add]
      norm_num
    linear_combination
      (-3 + 3 * LaurentPolynomial.T (-1) - LaurentPolynomial.T (-1) ^ 2) * ht
  · simp

/-- The infinity chart is explicitly equivalent to the original torus algebra. -/
def zeroInfinityTorusEquiv : Coordinate (equation (0 : R)) 1 ≃ₐ[R] R[T;T⁻¹] :=
  AlgEquiv.ofAlgHom zeroInfinityToTorus torusToZeroInfinity
    zeroInfinityToTorus_comp torusToZeroInfinity_comp

variable (K : Type*) [Field K]

/-- The original torus chart identifies with the chart containing the infinity section. -/
def zeroTorusChartIso : OneGonGluing.torusChart K ≅ chartScheme (equation (0 : K)) 1 :=
  Scheme.Spec.mapIso zeroInfinityTorusEquiv.toRingEquiv.toCommRingCatIso.op

/-- The chart identification preserves the coefficient structure map. -/
@[reassoc] theorem zeroTorusChartIso_structure :
    (zeroTorusChartIso K).hom ≫ chartStructure (equation (0 : K)) 1 =
      OneGonGluing.torusToBase K := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext zeroInfinityTorusEquiv.commutes

/-- Include the original torus in the actual zero-parameter cubic. -/
def zeroTorusInclusion : OneGonGluing.torusChart K ⟶ integralCurve (equation (0 : K)) :=
  (zeroTorusChartIso K).hom ≫ integralCurveChart (equation (0 : K)) 1

/-- The constructed torus inclusion is open. -/
instance zeroTorusInclusion_isOpenImmersion : IsOpenImmersion (zeroTorusInclusion K) := by
  dsimp [zeroTorusInclusion]
  infer_instance

/-- The torus inclusion lies over the original coefficient field. -/
@[reassoc] theorem zeroTorusInclusion_structure :
    zeroTorusInclusion K ≫ integralCurveStructure (equation (0 : K)) =
      OneGonGluing.torusToBase K := by
  rw [zeroTorusInclusion, Category.assoc, integralCurveChart_structure,
    zeroTorusChartIso_structure]

end FLT.Mazur.OneGonSmoothing

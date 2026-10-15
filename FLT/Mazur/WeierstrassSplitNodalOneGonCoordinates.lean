/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalOneGonIso
public import FLT.Mazur.WeierstrassSplitNodalProjectiveReflection

/-!
# The full one-gon comparison has the reciprocal smooth coordinate

The homogeneous scaling is checked on every Laurent function. Thus the
whole-cubic isomorphism extends the specified reciprocal torus comparison.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {K : Type} [Field K] (a : Kˣ)
local notation "L" => K[T;T⁻¹]
local notation "F" => (LaurentPolynomial.C : K →+* L)
local notation "Q" => (![1 - LaurentPolynomial.T (-1), 1,
  LaurentPolynomial.T 1 * (1 - LaurentPolynomial.T (-1)) ^ 3] : Fin 3 → L)
local notation "P" => (fun i => LaurentPolynomial.invert
  ((![splitNodalLaurentX a, 1, splitNodalLaurentZ a] : Fin 3 → L) i))
local notation "v" => (Units.map (F).toMonoidHom (-a))
local notation "ι" => Spec.map (CommRingCat.ofHom
  (LaurentPolynomial.invert (R := K)).toRingHom)

/-- The actual scaled homogeneous coordinates differ by the cube of a coefficient unit. -/
theorem splitNodalOneGonChange_coordinates :
    WeierstrassVariableChangeHomogeneous.coordinates ((splitNodalOneGonChange a).map F) Q =
      fun i => (↑(v ^ 3) : L) * P i := by
  have ha : F (a : K) * F (↑a⁻¹ : K) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  funext i
  fin_cases i
  · change F (-↑a) ^ 2 * (1 - LaurentPolynomial.T (-1)) + F 0 * _ =
      F (-↑a) ^ 3 * LaurentPolynomial.invert (splitNodalLaurentX a)
    simp only [map_neg, map_zero, zero_mul, add_zero, splitNodalLaurentX,
      map_mul, map_sub, map_one, LaurentPolynomial.invert_T,
      show algebraMap K L = LaurentPolynomial.C from rfl, LaurentPolynomial.invert_C]
    linear_combination
      (F (a : K)) ^ 2 * (LaurentPolynomial.T (-1) - 1) * ha
  · change F (-↑a) ^ 3 * 1 + F (-↑a) ^ 2 * F 0 * _ + F 0 * _ =
      F (-↑a) ^ 3 * LaurentPolynomial.invert 1
    simp
  · change LaurentPolynomial.T 1 * (1 - LaurentPolynomial.T (-1)) ^ 3 =
      F (-↑a) ^ 3 * LaurentPolynomial.invert (splitNodalLaurentZ a)
    simp only [map_neg, splitNodalLaurentZ, splitNodalLaurentX,
      map_mul, map_pow, map_sub, map_one, LaurentPolynomial.invert_T,
      show algebraMap K L = LaurentPolynomial.C from rfl, LaurentPolynomial.invert_C, neg_neg]
    calc
      _ = -(F (a : K) * F (↑a⁻¹ : K)) ^ 3 *
          (LaurentPolynomial.T (-1) - 1) ^ 3 * LaurentPolynomial.T 1 := by
        rw [ha]
        ring
      _ = _ := by ring

/-- The original zero-fiber torus has its displayed homogeneous coordinates. -/
@[reassoc] theorem zeroTorusInclusion_projectivePoint :
    OneGonSmoothing.zeroTorusInclusion K ≫
        integralProjectiveMap (OneGonSmoothing.equation (0 : K)) =
      ProjectiveSpace.unitChartPoint K (Fin 3) F Q 1 1 rfl := by
  rw [OneGonSmoothing.zeroTorusInclusion, Category.assoc,
    integralCurveChart_projectiveMap, projectiveChartMap_eq_unitChartPoint]
  change Spec.map (CommRingCat.ofHom OneGonSmoothing.zeroInfinityToTorus.toRingHom) ≫ _ = _
  rw [ProjectiveSpace.unitChartPoint_map]
  simp only [map_one]
  congr 1
  · exact OneGonSmoothing.zeroInfinityToTorus.comp_algebraMap
  · funext i
    exact evaluation_coord _ _ _ _ _ i

/-- The full cubic scaling restricts to the reciprocal original nodal torus. -/
@[reassoc] theorem splitNodalZeroCubicIso_torus :
    OneGonSmoothing.zeroTorusInclusion K ≫ (splitNodalZeroCubicIso a).hom =
      ι ≫ splitNodalTorusToCurve a := by
  apply (cancel_mono (integralProjectiveMap (splitNodalEquation a))).mp
  change (OneGonSmoothing.zeroTorusInclusion K ≫ integralVariableChangeTo _ _ _ _) ≫ _ = _
  rw [Category.assoc, integralVariableChangeTo_projectiveMap,
    zeroTorusInclusion_projectivePoint_assoc, Category.assoc,
    splitNodalTorus_projectivePoint, ProjectiveSpace.unitChartPoint_map]
  simp only [map_one]
  have hp : P 1 = (1 : Lˣ) := map_one _
  have hc : WeierstrassVariableChangeHomogeneous.coordinates
      ((splitNodalOneGonChange a).map F) Q 1 = (↑(v ^ 3) : L) := by
    simp only [splitNodalOneGonChange_coordinates, hp, Units.val_one, mul_one]
  rw [WeierstrassVariableChangeLinear.unitChartPoint_projectiveIso
    (splitNodalOneGonChange a) F Q 1 1 1 (v ^ 3) rfl hc]
  simp only [splitNodalOneGonChange_coordinates]
  convert ProjectiveSpace.unitChartPoint_scale K (Fin 3) F P 1 1 (v ^ 3) hp using 1
  · simp only [mul_one]
  · congr 1
    apply RingHom.ext
    exact LaurentPolynomial.invert_C

/-- The global pinching isomorphism extends precisely the reciprocal Laurent parameter. -/
@[reassoc] theorem splitNodalOneGonIso_torus :
    OneGonGluing.torus K ≫ (splitNodalOneGonIso a).hom =
      ι ≫ splitNodalTorusToCurve a := by
  rw [splitNodalOneGonIso, Iso.trans_hom, ← Category.assoc,
    OneGonSmoothing.torus_zeroFiberIso, splitNodalZeroCubicIso_torus]

end FLT.Mazur.WeierstrassIntegralChart

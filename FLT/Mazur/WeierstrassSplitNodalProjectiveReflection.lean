/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalLaurentReflection
public import FLT.Mazur.WeierstrassSplitNodalTorus
public import FLT.Mazur.WeierstrassVariableChangeProjectivePoints
public import FLT.Mazur.WeierstrassIntegralChartProjectivePoint

/-!
# Interchanging tangent roots preserves the entire original projective cubic map

The signed shear is compared on the full Laurent torus by homogeneous unit
rescaling, including the point at infinity and arbitrary coefficient algebras.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] (a : Rˣ)
local notation "L" => R[T;T⁻¹]
local notation "F" => (algebraMap R L)
local notation "P" => (![splitNodalLaurentX a, 1, splitNodalLaurentZ a] : Fin 3 → L)
local notation "C" => (VariableChange.mk 1 0 (-(a : R)) 0 : VariableChange R)
local notation "ι" => Spec.map (CommRingCat.ofHom
  (LaurentPolynomial.invert (R := R)).toRingHom)

/-- The full nodal torus map retains its normalized homogeneous coordinate tuple. -/
@[reassoc] theorem splitNodalTorus_projectivePoint :
    splitNodalTorusToCurve a ≫ integralProjectiveMap (splitNodalEquation a) =
      ProjectiveSpace.unitChartPoint R (Fin 3) F P 1 1 rfl := by
  rw [splitNodalTorusToCurve, Category.assoc, integralCurveChart_projectiveMap,
    projectiveChartMap_eq_unitChartPoint]
  change Spec.map (CommRingCat.ofHom (splitNodalChartToLaurent a).toRingHom) ≫ _ = _
  rw [ProjectiveSpace.unitChartPoint_map]
  simp only [map_one]
  congr 1
  · exact (splitNodalChartToLaurent a).comp_algebraMap
  · funext i
    exact splitNodalChartToLaurent_coord a i

/-- The actual signed projective shear and Laurent inversion preserve the entire cubic map. -/
theorem splitNodalTorus_projectiveReflection :
    ι ≫ splitNodalTorusToCurve (-a) ≫ integralProjectiveMap (splitNodalEquation (-a)) ≫
        (WeierstrassVariableChangeLinear.projectiveIso C).hom =
      splitNodalTorusToCurve a ≫ integralProjectiveMap (splitNodalEquation a) := by
  let Q : Fin 3 → L := fun i => LaurentPolynomial.invert
    ((![splitNodalLaurentX (-a), 1, splitNodalLaurentZ (-a)] : Fin 3 → L) i)
  let v : Lˣ := LaurentUnitPoints.pointUnit (AlgHom.id R L)
  have hv : (↑v⁻¹ : L) = LaurentPolynomial.T (-1) := rfl
  have hc : WeierstrassVariableChangeHomogeneous.coordinates ((C).map F) Q =
      fun i => (↑v⁻¹ : L) * P i := by
    funext i
    fin_cases i
    · change (F 1) ^ 2 * LaurentPolynomial.invert (splitNodalLaurentX (-a)) +
        F 0 * LaurentPolynomial.invert (splitNodalLaurentZ (-a)) =
          (↑v⁻¹ : L) * splitNodalLaurentX a
      simp only [map_one, one_pow, one_mul, map_zero, zero_mul, add_zero, hv,
        splitNodalLaurent_reflect_x]
    · change (F 1) ^ 3 * LaurentPolynomial.invert 1 +
        (F 1) ^ 2 * F (-(a : R)) * LaurentPolynomial.invert (splitNodalLaurentX (-a)) +
        F 0 * LaurentPolynomial.invert (splitNodalLaurentZ (-a)) = (↑v⁻¹ : L) * 1
      simpa only [map_one, one_pow, one_mul, map_zero, zero_mul, add_zero,
        map_neg, mul_one, hv, neg_mul, ← sub_eq_add_neg] using splitNodalLaurent_reflect_y a
    · change LaurentPolynomial.invert (splitNodalLaurentZ (-a)) =
        (↑v⁻¹ : L) * splitNodalLaurentZ a
      exact splitNodalLaurent_reflect_z a
  have hp : Q 1 = (1 : Lˣ) := by simp [Q]
  have hq : WeierstrassVariableChangeHomogeneous.coordinates ((C).map F) Q 1 =
      (↑v⁻¹ : L) := by rw [hc]; exact mul_one _
  rw [splitNodalTorus_projectivePoint_assoc, splitNodalTorus_projectivePoint]
  rw [← Category.assoc, ProjectiveSpace.unitChartPoint_map]
  have hf : (LaurentPolynomial.invert (R := R)).toRingHom.comp F = F := by
    apply RingHom.ext
    intro x
    exact LaurentPolynomial.invert_C x
  simp only [hf, map_one]
  change ProjectiveSpace.unitChartPoint R (Fin 3) F Q 1 1 hp ≫ _ = _
  rw [WeierstrassVariableChangeLinear.unitChartPoint_projectiveIso C F Q 1 1 1 v⁻¹ hp hq]
  simp only [hc]
  simpa only [mul_one] using
    ProjectiveSpace.unitChartPoint_scale R (Fin 3) F P 1 1 v⁻¹ rfl

end FLT.Mazur.WeierstrassIntegralChart

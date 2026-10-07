/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassProjectiveChartProduct
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Integral boundary values of the projective addition polynomials

The existing homogeneous addition polynomials specialize to the other input
at infinity over any commutative ring, with the expected projective scale.
Their output-Z open therefore contains both mixed affine/infinity zero sections.
The cubic identity on the whole product, and hence a map into the output
Weierstrass chart, is not asserted here.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- Left infinity specializes the polynomial addition law without reducedness assumptions. -/
theorem projectiveAdd_at_left_infinity (Q : Fin 3 → R) :
    W.toProjective.addXYZ ![0, 1, 0] Q = Q 2 • Q := by
  ext i
  fin_cases i <;>
    simp [Projective.addXYZ, Projective.addX, Projective.addY, Projective.addZ,
      Projective.negAddY, Projective.negY] <;> ring

/-- Right infinity gives the same projective point, with the opposite scale. -/
theorem projectiveAdd_at_right_infinity (P : Fin 3 → R) :
    W.toProjective.addXYZ P ![0, 1, 0] = -P 2 • P := by
  ext i
  fin_cases i <;>
    simp [Projective.addXYZ, Projective.addX, Projective.addY, Projective.addZ,
      Projective.negAddY, Projective.negY] <;> ring

/-- The existing homogeneous addition polynomials on an integral input-chart product. -/
def chartProductAdditionCoordinates (j k : Fin 3) : Fin 3 → ChartProduct W j k :=
  (W.map (algebraMap R (ChartProduct W j k))).toProjective.addXYZ
    (chartProductLeft W j k ∘ coord W j) (chartProductRight W j k ∘ coord W k)

/-- The product addition polynomials specialize along every algebra map. -/
theorem chartProductAdditionCoordinates_map (j k : Fin 3)
    (f : ChartProduct W j k →ₐ[R] S) :
    f ∘ chartProductAdditionCoordinates W j k =
      (W.map (algebraMap R S)).toProjective.addXYZ
        (f ∘ chartProductLeft W j k ∘ coord W j)
        (f ∘ chartProductRight W j k ∘ coord W k) := by
  have h := Projective.map_addXYZ
    (W' := (W.map (algebraMap R (ChartProduct W j k))).toProjective) f.toRingHom
    (chartProductLeft W j k ∘ coord W j) (chartProductRight W j k ∘ coord W k)
  have he : (W.map (algebraMap R (ChartProduct W j k))).map f.toRingHom =
      W.map (algebraMap R S) := by
    ext <;> exact f.commutes _
  change ((W.map (algebraMap R (ChartProduct W j k))).map f.toRingHom).toProjective.addXYZ
    _ _ = f ∘ chartProductAdditionCoordinates W j k at h
  rw [he] at h
  exact h.symm

/-- Along the left infinity section the output equals the other homogeneous input up to Z. -/
theorem chartProductAdditionCoordinates_left_infinity (k : Fin 3) :
    chartProductAtLeftInfinity W k ∘ chartProductAdditionCoordinates W 1 k =
      coord W k 2 • coord W k := by
  rw [chartProductAdditionCoordinates_map]
  have hl : chartProductAtLeftInfinity W k ∘ chartProductLeft W 1 k ∘ coord W 1 =
      ![0, 1, 0] := by
    funext i
    exact (DFunLike.congr_fun (chartProductAtLeftInfinity_left W k) (coord W 1 i)).trans
      (chartInfinityEvaluation_coord W i)
  have hr : chartProductAtLeftInfinity W k ∘ chartProductRight W 1 k ∘ coord W k =
      coord W k := by
    funext i
    exact DFunLike.congr_fun (chartProductAtLeftInfinity_right W k) (coord W k i)
  rw [hl, hr]
  exact projectiveAdd_at_left_infinity _ _

/-- Along the right infinity section the output has the opposite homogeneous scale. -/
theorem chartProductAdditionCoordinates_right_infinity (j : Fin 3) :
    chartProductAtRightInfinity W j ∘ chartProductAdditionCoordinates W j 1 =
      -coord W j 2 • coord W j := by
  rw [chartProductAdditionCoordinates_map]
  have hl : chartProductAtRightInfinity W j ∘ chartProductLeft W j 1 ∘ coord W j =
      coord W j := by
    funext i
    exact DFunLike.congr_fun (chartProductAtRightInfinity_left W j) (coord W j i)
  have hr : chartProductAtRightInfinity W j ∘ chartProductRight W j 1 ∘ coord W 1 =
      ![0, 1, 0] := by
    funext i
    exact (DFunLike.congr_fun (chartProductAtRightInfinity_right W j) (coord W 1 i)).trans
      (chartInfinityEvaluation_coord W i)
  rw [hl, hr]
  exact projectiveAdd_at_right_infinity _ _

/-- The polynomial output-Z open does not discard any point of the left infinity section. -/
theorem chartProductAdditionCoordinates_left_z :
    chartProductAtLeftInfinity W 2 (chartProductAdditionCoordinates W 1 2 2) = 1 := by
  simpa only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, coord_self, one_mul] using
    congrFun (chartProductAdditionCoordinates_left_infinity W 2) 2

/-- The polynomial output-Z open also contains the right infinity section. -/
theorem chartProductAdditionCoordinates_right_z :
    chartProductAtRightInfinity W 2 (chartProductAdditionCoordinates W 2 1 2) = -1 := by
  simpa only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, coord_self, mul_one] using
    congrFun (chartProductAdditionCoordinates_right_infinity W 2) 2

/-- Lift the whole left infinity section through the polynomial output-Z localization. -/
def chartProductLeftInfinityLift :
    Localization.Away (chartProductAdditionCoordinates W 1 2 2) →ₐ[R] Coordinate W 2 :=
  IsLocalization.Away.liftAlgHom (chartProductAdditionCoordinates W 1 2 2)
    (show IsUnit (chartProductAtLeftInfinity W 2
      (chartProductAdditionCoordinates W 1 2 2)) by
        rw [chartProductAdditionCoordinates_left_z]
        exact isUnit_one)

/-- Lift the whole right infinity section through the polynomial output-Z localization. -/
def chartProductRightInfinityLift :
    Localization.Away (chartProductAdditionCoordinates W 2 1 2) →ₐ[R] Coordinate W 2 :=
  IsLocalization.Away.liftAlgHom (chartProductAdditionCoordinates W 2 1 2)
    (show IsUnit (chartProductAtRightInfinity W 2
      (chartProductAdditionCoordinates W 2 1 2)) by
        rw [chartProductAdditionCoordinates_right_z]
        exact (isUnit_one : IsUnit (1 : Coordinate W 2)).neg)

/-- The lifted left section restricts to the original product section. -/
@[simp] theorem chartProductLeftInfinityLift_restriction (a : ChartProduct W 1 2) :
    chartProductLeftInfinityLift W
      (algebraMap _ (Localization.Away (chartProductAdditionCoordinates W 1 2 2)) a) =
      chartProductAtLeftInfinity W 2 a := by
  simp only [chartProductLeftInfinityLift, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- The lifted right section restricts to the original product section. -/
@[simp] theorem chartProductRightInfinityLift_restriction (a : ChartProduct W 2 1) :
    chartProductRightInfinityLift W
      (algebraMap _ (Localization.Away (chartProductAdditionCoordinates W 2 1 2)) a) =
      chartProductAtRightInfinity W 2 a := by
  simp only [chartProductRightInfinityLift, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

end FLT.Mazur.WeierstrassIntegralChart

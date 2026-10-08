/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendreBraidCover

/-! # The common Legendre cover is a domain

The conic parameter t = w/(1+v), where v²+w²=1, defines a map from
a localization of the Gaussian polynomial ring to the actual triple cover.
Explicit formulas for v and w define a map back. Their composition fixes
the three roots, giving an injection of the cover into a domain.
This supplies the domain hypothesis for cyclic parameters on the common
cover; the mixed relation still needs to be descended globally.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
variable {R : Type*} [CommRing R]

theorem conic_one_add_isUnit (v w : Rˣ)
    (h : (v : R) ^ 2 + (w : R) ^ 2 = 1) : IsUnit (1 + (v : R)) := by
  have he : (1 + (v : R)) * (1 - (v : R)) = (w : R) ^ 2 := by
    linear_combination -h
  exact (IsUnit.mul_iff.mp (he ▸ (w.isUnit.pow 2))).1

/-- The invertible conic parameter w/(1+v). -/
def conicChartUnit (v w : Rˣ)
    (h : (v : R) ^ 2 + (w : R) ^ 2 = 1) : Rˣ :=
  w * (conic_one_add_isUnit v w h).unit⁻¹

theorem conicChartUnit_mul (v w : Rˣ)
    (h : (v : R) ^ 2 + (w : R) ^ 2 = 1) :
    (conicChartUnit v w h : R) * (1 + (v : R)) = (w : R) := by
  change ((w * (conic_one_add_isUnit v w h).unit⁻¹ : Rˣ) : R) * _ = _
  rw [Units.val_mul, mul_assoc]
  have hi : (((conic_one_add_isUnit v w h).unit⁻¹ : Rˣ) : R) * (1 + (v : R)) = 1 := by
    simpa only [IsUnit.unit_spec] using (conic_one_add_isUnit v w h).unit.inv_mul
  rw [hi, mul_one]

theorem conicChartUnit_square_mul (v w : Rˣ)
    (h : (v : R) ^ 2 + (w : R) ^ 2 = 1) :
    (conicChartUnit v w h : R) ^ 2 * (1 + (v : R)) = 1 - (v : R) := by
  apply (conic_one_add_isUnit v w h).mul_left_injective
  have ht := congrArg (fun x : R => x^2) (conicChartUnit_mul v w h)
  linear_combination ht + h

theorem conicChartUnit_denominator (v w : Rˣ)
    (h : (v : R) ^ 2 + (w : R) ^ 2 = 1) :
    (1 + (conicChartUnit v w h : R) ^ 2) * (1 + (v : R)) = 2 := by
  have ht := conicChartUnit_square_mul v w h
  linear_combination ht

theorem conicChartUnit_numerator (v w : Rˣ)
    (h : (v : R) ^ 2 + (w : R) ^ 2 = 1) :
    (1 - (conicChartUnit v w h : R) ^ 2) * (1 + (v : R)) = 2 * (v : R) := by
  have ht := conicChartUnit_square_mul v w h
  linear_combination -ht

theorem conicChartUnit_denominator_isUnit (v w : Rˣ)
    (h : (v : R) ^ 2 + (w : R) ^ 2 = 1) (h2 : IsUnit (2 : R)) :
    IsUnit (1 + (conicChartUnit v w h : R) ^ 2) := by
  exact (IsUnit.mul_iff.mp ((conicChartUnit_denominator v w h) ▸ h2)).1

theorem conicChartUnit_numerator_isUnit (v w : Rˣ)
    (h : (v : R) ^ 2 + (w : R) ^ 2 = 1) (h2 : IsUnit (2 : R)) :
    IsUnit (1 - (conicChartUnit v w h : R) ^ 2) := by
  exact (IsUnit.mul_iff.mp ((conicChartUnit_numerator v w h) ▸ h2.mul v.isUnit)).1

theorem conicChartUnit_recover_v (v w : Rˣ)
    (h : (v : R) ^ 2 + (w : R) ^ 2 = 1) :
    (1 + (conicChartUnit v w h : R) ^ 2) * (v : R) =
      1 - (conicChartUnit v w h : R) ^ 2 := by
  have ht := conicChartUnit_square_mul v w h
  linear_combination ht

theorem conicChartUnit_recover_w (v w : Rˣ)
    (h : (v : R) ^ 2 + (w : R) ^ 2 = 1) :
    (1 + (conicChartUnit v w h : R) ^ 2) * (w : R) =
      2 * (conicChartUnit v w h : R) := by
  rw [← conicChartUnit_mul v w h]
  linear_combination (conicChartUnit v w h : R) * conicChartUnit_denominator v w h


open Polynomial

theorem legendreBraid_conic (p : ℕ) :
    (legendreBraidComplementRoot p : LegendreBraidRing p) ^ 2 +
      (legendreBraidParameterRoot p : LegendreBraidRing p) ^ 2 = 1 := by
  rw [legendreBraidComplementRoot_square, legendreBraidParameterRoot_square]
  ring

/-- The conic parameter on the common Legendre cover. -/
def legendreBraidChartUnit (p : ℕ) : (LegendreBraidRing p)ˣ :=
  conicChartUnit (legendreBraidComplementRoot p) (legendreBraidParameterRoot p)
    (legendreBraid_conic p)

/-- The product inverted in the conic polynomial presentation. -/
def braidRootDenominator (p : ℕ) : GaussianInt[X] :=
  2 * (p : GaussianInt[X]) * X * (1 + X ^ 2) * (1 - X ^ 2)

/-- The localized Gaussian polynomial domain for the common cover. -/
abbrev LegendreBraidPolynomialRing (p : ℕ) :=
  Localization.Away (braidRootDenominator p)

instance legendreBraidPolynomialDomain (p : ℕ) [NeZero p] :
    IsDomain (LegendreBraidPolynomialRing p) :=
  Localization.Away.isDomain (by
    dsimp [braidRootDenominator]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (mul_ne_zero (by norm_num)
          (by exact_mod_cast NeZero.ne p)) X_ne_zero
      · intro h
        have hh := congrArg (fun q : GaussianInt[X] => q.eval 0) h
        norm_num at hh
    · intro h
      have hh := congrArg (fun q : GaussianInt[X] => q.eval 0) h
      norm_num at hh)

/-- The polynomial parameter in the localized conic chart. -/
def braidRootParameter (p : ℕ) : LegendreBraidPolynomialRing p :=
  algebraMap GaussianInt[X] (LegendreBraidPolynomialRing p) X

/-- The Gaussian coefficients in the localized conic chart. -/
def braidConstantMap (p : ℕ) : GaussianInt →+* LegendreBraidPolynomialRing p :=
  (algebraMap GaussianInt[X] (LegendreBraidPolynomialRing p)).comp C

theorem braidRootParameter_units (p : ℕ) :
    IsUnit (2 : LegendreBraidPolynomialRing p) ∧
      IsUnit (p : LegendreBraidPolynomialRing p) ∧
      IsUnit (braidRootParameter p) ∧
      IsUnit (1 + braidRootParameter p ^ 2) ∧
      IsUnit (1 - braidRootParameter p ^ 2) := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := LegendreBraidPolynomialRing p) (braidRootDenominator p)
  simpa only [braidRootDenominator, map_mul, map_ofNat, map_natCast, map_sub,
    map_add, map_pow, map_one, braidRootParameter, IsUnit.mul_iff, and_assoc] using h

/-- Gaussian coefficients evaluated at the minus-one root of the common cover. -/
def braidGaussianMap (p : ℕ) : GaussianInt →+* LegendreBraidRing p :=
  Zsqrtd.lift (d := -1) ⟨(legendreBraidMinusOneRoot p : LegendreBraidRing p), by
    simpa only [← pow_two, Int.cast_neg, Int.cast_one] using
      legendreBraidMinusOneRoot_square p⟩

theorem braidGaussianMap_root (p : ℕ) :
    braidGaussianMap p (Zsqrtd.sqrtd (d := -1)) =
      (legendreBraidMinusOneRoot p : LegendreBraidRing p) := by
  simp [braidGaussianMap]

theorem legendreBraidChart_units (p : ℕ) :
    IsUnit (2 : LegendreBraidRing p) ∧ IsUnit (p : LegendreBraidRing p) ∧
      IsUnit (legendreBraidChartUnit p : LegendreBraidRing p) ∧
      IsUnit (1 + (legendreBraidChartUnit p : LegendreBraidRing p) ^ 2) ∧
      IsUnit (1 - (legendreBraidChartUnit p : LegendreBraidRing p) ^ 2) := by
  have h2 : IsUnit (2 : LegendreBraidRing p) := by
    simpa only [map_ofNat] using (legendreBase_units p).1.map
      (algebraMap (LegendreBase p) (LegendreBraidRing p))
  exact ⟨h2, Fact.out, (legendreBraidChartUnit p).isUnit,
    conicChartUnit_denominator_isUnit _ _ (legendreBraid_conic p) h2,
    conicChartUnit_numerator_isUnit _ _ (legendreBraid_conic p) h2⟩

/-- Evaluation of the localized conic chart on the actual cover. -/
def legendreBraidFromPolynomial (p : ℕ) :
    LegendreBraidPolynomialRing p →+* LegendreBraidRing p :=
  IsLocalization.Away.lift (braidRootDenominator p)
    (show IsUnit ((eval₂RingHom (braidGaussianMap p)
      (legendreBraidChartUnit p : LegendreBraidRing p)) (braidRootDenominator p)) by
      have h := legendreBraidChart_units p
      simpa only [braidRootDenominator, map_mul, map_ofNat, map_natCast, map_sub,
        map_add, map_pow, map_one, coe_eval₂RingHom, eval₂_X] using
        (((h.1.mul h.2.1).mul h.2.2.1).mul h.2.2.2.1).mul h.2.2.2.2)

theorem legendreBraidFromPolynomial_parameter (p : ℕ) :
    legendreBraidFromPolynomial p (braidRootParameter p) =
      (legendreBraidChartUnit p : LegendreBraidRing p) := by
  change ((legendreBraidFromPolynomial p).comp
    (algebraMap GaussianInt[X] (LegendreBraidPolynomialRing p))) X = _
  rw [legendreBraidFromPolynomial, IsLocalization.Away.lift_comp]
  simp

theorem legendreBraidFromPolynomial_constant (p : ℕ) (a : GaussianInt) :
    legendreBraidFromPolynomial p (braidConstantMap p a) = braidGaussianMap p a := by
  change ((legendreBraidFromPolynomial p).comp
    (algebraMap GaussianInt[X] (LegendreBraidPolynomialRing p))) (C a) = _
  rw [legendreBraidFromPolynomial, IsLocalization.Away.lift_comp]
  simp


/-- The root 2t/(1+t²) of the Legendre parameter. -/
def braidPolynomialParameterRoot (p : ℕ) : (LegendreBraidPolynomialRing p)ˣ :=
  (braidRootParameter_units p).1.unit * (braidRootParameter_units p).2.2.1.unit *
    (braidRootParameter_units p).2.2.2.1.unit⁻¹

/-- The root (1-t²)/(1+t²) of the complementary parameter. -/
def braidPolynomialComplementRoot (p : ℕ) : (LegendreBraidPolynomialRing p)ˣ :=
  (braidRootParameter_units p).2.2.2.2.unit * (braidRootParameter_units p).2.2.2.1.unit⁻¹

theorem braidPolynomialParameterRoot_mul (p : ℕ) :
    (braidPolynomialParameterRoot p : LegendreBraidPolynomialRing p) *
      (1 + braidRootParameter p ^ 2) = 2 * braidRootParameter p := by
  have hi := (braidRootParameter_units p).2.2.2.1.unit.inv_mul
  simp only [IsUnit.unit_spec] at hi
  simp only [braidPolynomialParameterRoot, Units.val_mul, IsUnit.unit_spec]
  rw [mul_assoc, hi, mul_one]

theorem braidPolynomialComplementRoot_mul (p : ℕ) :
    (braidPolynomialComplementRoot p : LegendreBraidPolynomialRing p) *
      (1 + braidRootParameter p ^ 2) = 1 - braidRootParameter p ^ 2 := by
  have hi := (braidRootParameter_units p).2.2.2.1.unit.inv_mul
  simp only [IsUnit.unit_spec] at hi
  simp only [braidPolynomialComplementRoot, Units.val_mul, IsUnit.unit_spec]
  rw [mul_assoc, hi, mul_one]

theorem braidPolynomialRoots_conic (p : ℕ) :
    (braidPolynomialComplementRoot p : LegendreBraidPolynomialRing p) ^ 2 +
      (braidPolynomialParameterRoot p : LegendreBraidPolynomialRing p) ^ 2 = 1 := by
  apply ((braidRootParameter_units p).2.2.2.1.pow 2).mul_left_injective
  calc
    _ = ((braidPolynomialComplementRoot p : LegendreBraidPolynomialRing p) *
          (1 + braidRootParameter p ^ 2)) ^ 2 +
        ((braidPolynomialParameterRoot p : LegendreBraidPolynomialRing p) *
          (1 + braidRootParameter p ^ 2)) ^ 2 := by ring
    _ = _ := by rw [braidPolynomialComplementRoot_mul, braidPolynomialParameterRoot_mul]; ring

theorem legendreBraidFromPolynomial_parameterRoot (p : ℕ) :
    legendreBraidFromPolynomial p
      (braidPolynomialParameterRoot p : LegendreBraidPolynomialRing p) =
        (legendreBraidParameterRoot p : LegendreBraidRing p) := by
  apply (legendreBraidChart_units p).2.2.2.1.mul_left_inj.mp
  have he := congrArg (legendreBraidFromPolynomial p) (braidPolynomialParameterRoot_mul p)
  simp only [map_mul, map_add, map_pow, map_one, map_ofNat,
    legendreBraidFromPolynomial_parameter] at he
  rw [he]
  simpa only [legendreBraidChartUnit, mul_comm] using
    (conicChartUnit_recover_w _ _ (legendreBraid_conic p)).symm

theorem legendreBraidFromPolynomial_complementRoot (p : ℕ) :
    legendreBraidFromPolynomial p
      (braidPolynomialComplementRoot p : LegendreBraidPolynomialRing p) =
        (legendreBraidComplementRoot p : LegendreBraidRing p) := by
  apply (legendreBraidChart_units p).2.2.2.1.mul_left_inj.mp
  have he := congrArg (legendreBraidFromPolynomial p) (braidPolynomialComplementRoot_mul p)
  simp only [map_mul, map_add, map_pow, map_one, map_sub,
    legendreBraidFromPolynomial_parameter] at he
  rw [he, mul_comm]
  exact (conicChartUnit_recover_v _ _ (legendreBraid_conic p)).symm

/-- The Legendre base map into the conic chart. -/
def legendreBraidPolynomialMap (p : ℕ) :
    LegendreBase p →+* LegendreBraidPolynomialRing p :=
  legendreSpecialize p
    ((braidPolynomialParameterRoot p : LegendreBraidPolynomialRing p) ^ 2)
    (braidRootParameter_units p).1 (braidRootParameter_units p).2.1
    ((braidPolynomialParameterRoot p).isUnit.pow 2) (by
      have he : (braidPolynomialParameterRoot p : LegendreBraidPolynomialRing p) ^ 2 - 1 =
          -(braidPolynomialComplementRoot p : LegendreBraidPolynomialRing p) ^ 2 := by
        linear_combination braidPolynomialRoots_conic p
      rw [he]
      exact ((braidPolynomialComplementRoot p).isUnit.pow 2).neg)

instance legendreBraidPolynomialAlgebra (p : ℕ) :
    Algebra (LegendreBase p) (LegendreBraidPolynomialRing p) :=
  (legendreBraidPolynomialMap p).toAlgebra

theorem legendreBraidPolynomialMap_parameter (p : ℕ) :
    algebraMap (LegendreBase p) (LegendreBraidPolynomialRing p) (legendreParameter p) =
      (braidPolynomialParameterRoot p : LegendreBraidPolynomialRing p) ^ 2 := by
  apply legendreSpecialize_parameter
  · exact (braidRootParameter_units p).1
  · exact (braidRootParameter_units p).2.1
  · exact (braidPolynomialParameterRoot p).isUnit.pow 2
  · have he : (braidPolynomialParameterRoot p : LegendreBraidPolynomialRing p) ^ 2 - 1 =
        -(braidPolynomialComplementRoot p : LegendreBraidPolynomialRing p) ^ 2 := by
      linear_combination braidPolynomialRoots_conic p
    rw [he]
    exact ((braidPolynomialComplementRoot p).isUnit.pow 2).neg

theorem legendreBraidFromPolynomial_base (p : ℕ) :
    (legendreBraidFromPolynomial p).comp
        (algebraMap (LegendreBase p) (LegendreBraidPolynomialRing p)) =
      algebraMap (LegendreBase p) (LegendreBraidRing p) := by
  apply legendreRingHom_ext p
  rw [RingHom.comp_apply, legendreBraidPolynomialMap_parameter, map_pow,
    legendreBraidFromPolynomial_parameterRoot, legendreBraidParameterRoot_square]

/-- Conic evaluation as a map of Legendre algebras. -/
def legendreBraidFromPolynomialAlg (p : ℕ) :
    LegendreBraidPolynomialRing p →ₐ[LegendreBase p] LegendreBraidRing p where
  __ := legendreBraidFromPolynomial p
  commutes' x := DFunLike.congr_fun (legendreBraidFromPolynomial_base p) x

/-- The quadratic etale map defined by an invertible root with invertible two. -/
def quadraticUnitLift {S : Type*} [CommRing S] [Algebra R S]
    (d : Rˣ) (r : Sˣ) (h2 : IsUnit (2 : S)) (hr : (r : S) ^ 2 = algebraMap R S (d : R)) :
    QuadraticEtaleRing d →ₐ[R] S :=
  (quadraticEtalePair d).lift (r : S) (by
    constructor
    · change aeval (r : S) (X ^ 2 - C (d : R)) = 0
      simp only [map_sub, map_pow, aeval_X, aeval_C, hr, sub_self]
    · have hd : (quadraticRootPolynomial d).derivative = 2 * X := by
        simp [quadraticRootPolynomial]
        ring
      change IsUnit (aeval (r : S) (quadraticRootPolynomial d).derivative)
      rw [hd, map_mul, map_ofNat, aeval_X]
      exact h2.mul r.isUnit)

theorem quadraticUnitLift_unit {S : Type*} [CommRing S] [Algebra R S]
    (d : Rˣ) (r : Sˣ) (h2 : IsUnit (2 : S)) (hr : (r : S) ^ 2 = algebraMap R S (d : R)) :
    quadraticUnitLift d r h2 hr (quadraticEtaleUnit d : QuadraticEtaleRing d) = r := by
  simpa only [quadraticUnitLift, quadraticEtaleUnit, IsUnit.unit_spec] using
    StandardEtalePair.lift_X (quadraticEtalePair d) (r : S) _


theorem braidPolynomialMinusOne_square (p : ℕ) :
    braidConstantMap p (Zsqrtd.sqrtd (d := -1)) ^ 2 = -1 := by
  rw [← map_pow, pow_two, Zsqrtd.dmuld]
  simp

/-- The Gaussian root of minus one as a unit of the conic chart. -/
def braidPolynomialMinusOneRoot (p : ℕ) : (LegendreBraidPolynomialRing p)ˣ :=
  (show IsUnit (braidConstantMap p (Zsqrtd.sqrtd (d := -1))) from by
    apply (isUnit_pow_iff (by decide : 2 ≠ 0)).mp
    rw [braidPolynomialMinusOne_square]
    exact isUnit_one.neg).unit

theorem braidPolynomialMinusOneRoot_val (p : ℕ) :
    (braidPolynomialMinusOneRoot p : LegendreBraidPolynomialRing p) =
      braidConstantMap p (Zsqrtd.sqrtd (d := -1)) := IsUnit.unit_spec _

/-- The first quadratic factor evaluated at the Gaussian root. -/
def braidFirstLift (p : ℕ) :
    QuadraticEtaleRing (-1 : (LegendreBase p)ˣ) →ₐ[LegendreBase p]
      LegendreBraidPolynomialRing p :=
  quadraticUnitLift (-1) (braidPolynomialMinusOneRoot p) (braidRootParameter_units p).1
    (by rw [braidPolynomialMinusOneRoot_val, braidPolynomialMinusOne_square]
        simp only [Units.val_neg, Units.val_one, map_neg, map_one])

/-- The second quadratic factor evaluated at 2t/(1+t²). -/
def braidSecondLift (p : ℕ) :
    QuadraticEtaleRing (legendreParameterUnit p) →ₐ[LegendreBase p]
      LegendreBraidPolynomialRing p :=
  quadraticUnitLift (legendreParameterUnit p) (braidPolynomialParameterRoot p)
    (braidRootParameter_units p).1
    (by rw [legendreParameterUnit_val, legendreBraidPolynomialMap_parameter])

/-- The third quadratic factor evaluated at (1-t²)/(1+t²). -/
def braidThirdLift (p : ℕ) :
    QuadraticEtaleRing (legendreComplementUnit p) →ₐ[LegendreBase p]
      LegendreBraidPolynomialRing p :=
  quadraticUnitLift (legendreComplementUnit p) (braidPolynomialComplementRoot p)
    (braidRootParameter_units p).1
    (by rw [legendreComplementUnit_val, map_sub, map_one,
          legendreBraidPolynomialMap_parameter]
        linear_combination braidPolynomialRoots_conic p)

/-- The actual common cover mapped into the conic polynomial chart. -/
def legendreBraidToPolynomial (p : ℕ) :
    LegendreBraidRing p →ₐ[LegendreBase p] LegendreBraidPolynomialRing p :=
  Algebra.TensorProduct.lift
    (Algebra.TensorProduct.lift (braidFirstLift p) (braidSecondLift p) (fun _ _ => .all _ _))
    (braidThirdLift p) (fun _ _ => .all _ _)


open scoped TensorProduct
theorem legendreBraidToPolynomial_first (p : ℕ) :
    legendreBraidToPolynomial p (legendreBraidMinusOneRoot p : LegendreBraidRing p) =
      (braidPolynomialMinusOneRoot p : LegendreBraidPolynomialRing p) := by
  change legendreBraidToPolynomial p
    (((quadraticEtaleUnit (-1 : (LegendreBase p)ˣ) : QuadraticEtaleRing _) ⊗ₜ[LegendreBase p] 1)
      ⊗ₜ[LegendreBase p] 1) = _
  simp only [legendreBraidToPolynomial, Algebra.TensorProduct.lift_tmul, map_one,
    mul_one, braidFirstLift, quadraticUnitLift_unit]

theorem legendreBraidToPolynomial_second (p : ℕ) :
    legendreBraidToPolynomial p (legendreBraidParameterRoot p : LegendreBraidRing p) =
      (braidPolynomialParameterRoot p : LegendreBraidPolynomialRing p) := by
  change legendreBraidToPolynomial p
    ((1 ⊗ₜ[LegendreBase p] (quadraticEtaleUnit (legendreParameterUnit p) : QuadraticEtaleRing _))
      ⊗ₜ[LegendreBase p] 1) = _
  simp only [legendreBraidToPolynomial, Algebra.TensorProduct.lift_tmul, map_one,
    mul_one, one_mul, braidSecondLift, quadraticUnitLift_unit]

theorem legendreBraidToPolynomial_third (p : ℕ) :
    legendreBraidToPolynomial p (legendreBraidComplementRoot p : LegendreBraidRing p) =
      (braidPolynomialComplementRoot p : LegendreBraidPolynomialRing p) := by
  change legendreBraidToPolynomial p
    (1 ⊗ₜ[LegendreBase p]
      (quadraticEtaleUnit (legendreComplementUnit p) : QuadraticEtaleRing _)) = _
  simp only [legendreBraidToPolynomial, Algebra.TensorProduct.lift_tmul, map_one,
    one_mul, braidThirdLift, quadraticUnitLift_unit]

theorem quadraticTripleHom_ext {S : Type*} [CommRing S] [Algebra R S]
    (d e f : Rˣ) (F G : QuadraticTripleRing d e f →ₐ[R] S)
    (h1 : F (quadraticTripleFirstRoot d e f : QuadraticTripleRing d e f) =
      G (quadraticTripleFirstRoot d e f : QuadraticTripleRing d e f))
    (h2 : F (quadraticTripleSecondRoot d e f : QuadraticTripleRing d e f) =
      G (quadraticTripleSecondRoot d e f : QuadraticTripleRing d e f))
    (h3 : F (quadraticTripleThirdRoot d e f : QuadraticTripleRing d e f) =
      G (quadraticTripleThirdRoot d e f : QuadraticTripleRing d e f)) : F = G := by
  apply Algebra.TensorProduct.ext
  · apply Algebra.TensorProduct.ext
    · apply (quadraticEtalePair d).hom_ext
      change F (((quadraticEtalePair d).X ⊗ₜ[R] 1) ⊗ₜ[R] 1) =
        G (((quadraticEtalePair d).X ⊗ₜ[R] 1) ⊗ₜ[R] 1)
      change F (((quadraticEtaleUnit d : QuadraticEtaleRing d) ⊗ₜ[R] 1) ⊗ₜ[R] 1) =
        G (((quadraticEtaleUnit d : QuadraticEtaleRing d) ⊗ₜ[R] 1) ⊗ₜ[R] 1) at h1
      simpa only [quadraticEtaleUnit, IsUnit.unit_spec] using h1
    · apply (quadraticEtalePair e).hom_ext
      change F ((1 ⊗ₜ[R] (quadraticEtalePair e).X) ⊗ₜ[R] 1) =
        G ((1 ⊗ₜ[R] (quadraticEtalePair e).X) ⊗ₜ[R] 1)
      change F ((1 ⊗ₜ[R] (quadraticEtaleUnit e : QuadraticEtaleRing e)) ⊗ₜ[R] 1) =
        G ((1 ⊗ₜ[R] (quadraticEtaleUnit e : QuadraticEtaleRing e)) ⊗ₜ[R] 1) at h2
      simpa only [quadraticEtaleUnit, IsUnit.unit_spec] using h2
  · apply (quadraticEtalePair f).hom_ext
    change F (1 ⊗ₜ[R] (quadraticEtalePair f).X) = G (1 ⊗ₜ[R] (quadraticEtalePair f).X)
    change F (1 ⊗ₜ[R] (quadraticEtaleUnit f : QuadraticEtaleRing f)) =
      G (1 ⊗ₜ[R] (quadraticEtaleUnit f : QuadraticEtaleRing f)) at h3
    simpa only [quadraticEtaleUnit, IsUnit.unit_spec] using h3

theorem legendreBraidFromTo (p : ℕ) :
    (legendreBraidFromPolynomialAlg p).comp (legendreBraidToPolynomial p) =
      AlgHom.id (LegendreBase p) (LegendreBraidRing p) := by
  apply quadraticTripleHom_ext
  · change legendreBraidFromPolynomial p
      (legendreBraidToPolynomial p (legendreBraidMinusOneRoot p : LegendreBraidRing p)) = _
    rw [legendreBraidToPolynomial_first, braidPolynomialMinusOneRoot_val,
      legendreBraidFromPolynomial_constant, braidGaussianMap_root]
    rfl
  · change legendreBraidFromPolynomial p
      (legendreBraidToPolynomial p (legendreBraidParameterRoot p : LegendreBraidRing p)) = _
    rw [legendreBraidToPolynomial_second, legendreBraidFromPolynomial_parameterRoot]
    rfl
  · change legendreBraidFromPolynomial p
      (legendreBraidToPolynomial p (legendreBraidComplementRoot p : LegendreBraidRing p)) = _
    rw [legendreBraidToPolynomial_third, legendreBraidFromPolynomial_complementRoot]
    rfl

theorem legendreBraidToPolynomial_injective (p : ℕ) :
    Function.Injective (legendreBraidToPolynomial p) := by
  have h : Function.LeftInverse (legendreBraidFromPolynomialAlg p)
      (legendreBraidToPolynomial p) := fun x => AlgHom.congr_fun (legendreBraidFromTo p) x
  exact h.injective

instance legendreBraidDomain (p : ℕ) [NeZero p] : IsDomain (LegendreBraidRing p) :=
  Function.Injective.isDomain (legendreBraidToPolynomial p) (legendreBraidToPolynomial_injective p)

/-- The actual cyclic parameter cover after adjoining the three Legendre roots. -/
def legendreBraidCyclicCover (p : ℕ) [Fact p.Prime] :
    (scalarQuotientModel ((legendreModel p).map
      (algebraMap (LegendreBase p) (LegendreBraidRing p))) p).left ⟶
        (scalarQuotientModel (legendreModel p) p).left :=
  coefficientScalarQuotientMorphism (legendreModel p) (LegendreBraidRing p) p

end WeierstrassCurve.CubicCharts

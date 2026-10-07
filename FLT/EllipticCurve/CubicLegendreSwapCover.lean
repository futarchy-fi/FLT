/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendreParameterSymmetries
public import FLT.EllipticCurve.CubicCyclicSign
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
/-! # The integral swap square-root cover

The standard étale cover adjoining √(-1) to the universal Legendre base
is explicitly isomorphic to ℤ[i][λ, 1/(2pλ(λ-1))].
The inverse maps establish that the actual cover is a noetherian domain.
It carries the cyclic transport for λ ↦ 1-λ, independent of root sign
at prime level.
-/

open AlgebraicGeometry CategoryTheory Polynomial
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
/-- The product inverted in the Gaussian polynomial chart. -/
def swapRootDenominator (p : ℕ) : GaussianInt[X] := 2 * (p : GaussianInt[X]) * X * (X - 1)
/-- The polynomial presentation of the universal swap cover. -/
abbrev LegendreSwapPolynomialRing (p : ℕ) := Localization.Away (swapRootDenominator p)
instance legendreSwapPolynomialDomain (p : ℕ) [NeZero p] :
    IsDomain (LegendreSwapPolynomialRing p) :=
  Localization.Away.isDomain (by
    dsimp [swapRootDenominator]
    apply mul_ne_zero
    · exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast NeZero.ne p)) X_ne_zero
    · intro h
      have hh := congrArg (fun q : GaussianInt[X] => q.eval 0) h
      norm_num at hh)
/-- The Legendre coordinate in the Gaussian polynomial chart. -/
def swapRootParameter (p : ℕ) : LegendreSwapPolynomialRing p :=
  algebraMap GaussianInt[X] (LegendreSwapPolynomialRing p) X
/-- The Gaussian coefficient map into the localized polynomial ring. -/
def swapConstantMap (p : ℕ) : GaussianInt →+* LegendreSwapPolynomialRing p :=
  (algebraMap GaussianInt[X] (LegendreSwapPolynomialRing p)).comp C
/-- The distinguished Gaussian square root of minus one. -/
def swapRoot (p : ℕ) : LegendreSwapPolynomialRing p :=
  swapConstantMap p (Zsqrtd.sqrtd (d := -1))
/-- The Gaussian root satisfies its quadratic equation. -/
theorem swapRoot_square (p : ℕ) : swapRoot p ^ 2 = -1 := by
  rw [swapRoot, ← map_pow, pow_two, Zsqrtd.dmuld]
  simp
/-- The Gaussian root is a unit. -/
theorem swapRoot_isUnit (p : ℕ) : IsUnit (swapRoot p) := by
  apply (isUnit_pow_iff (by decide : 2 ≠ 0)).mp
  rw [swapRoot_square]
  exact isUnit_one.neg
/-- The four denominator factors are invertible. -/
theorem swapRootParameter_units (p : ℕ) :
    IsUnit (2 : LegendreSwapPolynomialRing p) ∧
      IsUnit (p : LegendreSwapPolynomialRing p) ∧
      IsUnit (swapRootParameter p) ∧ IsUnit (swapRootParameter p - 1) := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := LegendreSwapPolynomialRing p) (swapRootDenominator p)
  simpa only [swapRootDenominator, map_mul, map_ofNat, map_natCast, map_sub,
    map_one, swapRootParameter, IsUnit.mul_iff, and_assoc] using h
/-- The map from the universal Legendre base to the Gaussian chart. -/
def legendreSwapPolynomialMap (p : ℕ) :
    LegendreBase p →+* LegendreSwapPolynomialRing p :=
  legendreSpecialize p (swapRootParameter p)
    (swapRootParameter_units p).1 (swapRootParameter_units p).2.1
    (swapRootParameter_units p).2.2.1 (swapRootParameter_units p).2.2.2
instance legendreSwapPolynomialAlgebra (p : ℕ) :
    Algebra (LegendreBase p) (LegendreSwapPolynomialRing p) :=
  (legendreSwapPolynomialMap p).toAlgebra
/-- The base map preserves the Legendre parameter. -/
theorem legendreSwapPolynomialMap_parameter (p : ℕ) :
    algebraMap (LegendreBase p) (LegendreSwapPolynomialRing p) (legendreParameter p) =
      swapRootParameter p :=
  legendreSpecialize_parameter p (swapRootParameter p)
    (swapRootParameter_units p).1 (swapRootParameter_units p).2.1
    (swapRootParameter_units p).2.2.1 (swapRootParameter_units p).2.2.2
/-- The actual standard étale swap-cover algebra. -/
abbrev LegendreUniversalSwapRing (p : ℕ) := LegendreSwapRing (LegendreBase p)
private theorem quadraticDerivative {R : Type*} [CommRing R] (d : Rˣ) :
    (quadraticRootPolynomial d).derivative = 2 * X := by
  simp [quadraticRootPolynomial]
  ring
/-- The presentation map from the actual quadratic cover. -/
def legendreSwapToPolynomial (p : ℕ) :
    LegendreUniversalSwapRing p →ₐ[LegendreBase p] LegendreSwapPolynomialRing p :=
  (quadraticEtalePair (-1 : (LegendreBase p)ˣ)).lift (swapRoot p) (by
    constructor
    · change aeval (swapRoot p) (X ^ 2 - C ((-1 : (LegendreBase p)ˣ) : LegendreBase p)) = 0
      simp only [map_sub, map_pow, aeval_X, Units.val_neg, Units.val_one,
        map_neg, map_one, swapRoot_square, sub_self]
    · have hd := quadraticDerivative (-1 : (LegendreBase p)ˣ)
      change IsUnit (aeval (swapRoot p)
        (quadraticRootPolynomial (-1 : (LegendreBase p)ˣ)).derivative)
      rw [hd, map_mul, map_ofNat, aeval_X]
      exact (swapRootParameter_units p).1.mul (swapRoot_isUnit p))
/-- The distinguished étale root maps to the Gaussian root. -/
theorem legendreSwapToPolynomial_root (p : ℕ) :
    legendreSwapToPolynomial p (quadraticEtalePair (-1 : (LegendreBase p)ˣ)).X =
      swapRoot p := StandardEtalePair.lift_X _ _ _
/-- The distinguished root unit maps to the Gaussian root. -/
theorem legendreSwapToPolynomial_unit (p : ℕ) :
    legendreSwapToPolynomial p
      (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ) : LegendreUniversalSwapRing p) =
        swapRoot p := by
  simpa only [quadraticEtaleUnit, IsUnit.unit_spec] using legendreSwapToPolynomial_root p
/-- The quadratic equation in the actual swap cover. -/
theorem legendreSwapRoot_square (p : ℕ) :
    (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ) : LegendreUniversalSwapRing p) ^ 2 = -1 := by
  simpa only [Units.val_neg, Units.val_one, map_neg, map_one] using
    quadraticEtaleUnit_square (-1 : (LegendreBase p)ˣ)
/-- Gaussian coefficients evaluated at the distinguished étale root. -/
def swapGaussianMap (p : ℕ) : GaussianInt →+* LegendreUniversalSwapRing p :=
  Zsqrtd.lift (d := -1) ⟨(quadraticEtaleUnit (-1 : (LegendreBase p)ˣ) :
    LegendreUniversalSwapRing p), by
      simpa only [← pow_two, Int.cast_neg, Int.cast_one] using legendreSwapRoot_square p⟩
/-- Gaussian evaluation preserves the chosen root. -/
theorem swapGaussianMap_root (p : ℕ) :
    swapGaussianMap p (Zsqrtd.sqrtd (d := -1)) =
      (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ) : LegendreUniversalSwapRing p) := by
  simp [swapGaussianMap]
/-- The inverse presentation map, obtained by localization. -/
def legendreSwapFromPolynomial (p : ℕ) :
    LegendreSwapPolynomialRing p →+* LegendreUniversalSwapRing p :=
  IsLocalization.Away.lift (swapRootDenominator p)
    (show IsUnit ((eval₂RingHom (swapGaussianMap p)
      (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p) (legendreParameter p)))
        (swapRootDenominator p)) by
      have h := (((legendreBase_units p).1.mul (legendreBase_units p).2.1).mul
        (legendreBase_units p).2.2.1).mul (legendreBase_units p).2.2.2
      simpa only [swapRootDenominator, map_mul, map_ofNat, map_natCast, map_sub,
        map_one, coe_eval₂RingHom, eval₂_X] using
        h.map (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p)))
/-- The inverse map sends the parameter to its base image. -/
theorem legendreSwapFromPolynomial_parameter (p : ℕ) :
    legendreSwapFromPolynomial p (swapRootParameter p) =
      algebraMap (LegendreBase p) (LegendreUniversalSwapRing p) (legendreParameter p) := by
  change ((legendreSwapFromPolynomial p).comp
    (algebraMap GaussianInt[X] (LegendreSwapPolynomialRing p))) X = _
  rw [legendreSwapFromPolynomial, IsLocalization.Away.lift_comp]
  simp
/-- The inverse map sends the Gaussian root to the étale root. -/
theorem legendreSwapFromPolynomial_root (p : ℕ) :
    legendreSwapFromPolynomial p (swapRoot p) =
      (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ) : LegendreUniversalSwapRing p) := by
  change ((legendreSwapFromPolynomial p).comp
    (algebraMap GaussianInt[X] (LegendreSwapPolynomialRing p))) (C Zsqrtd.sqrtd) = _
  rw [legendreSwapFromPolynomial, IsLocalization.Away.lift_comp]
  simpa using swapGaussianMap_root p
/-- The inverse presentation respects the Legendre base. -/
theorem legendreSwapFromPolynomial_base (p : ℕ) :
    (legendreSwapFromPolynomial p).comp
        (algebraMap (LegendreBase p) (LegendreSwapPolynomialRing p)) =
      algebraMap (LegendreBase p) (LegendreUniversalSwapRing p) := by
  apply legendreRingHom_ext p
  rw [RingHom.comp_apply, legendreSwapPolynomialMap_parameter,
    legendreSwapFromPolynomial_parameter]
/-- The inverse presentation as a map of Legendre algebras. -/
def legendreSwapFromPolynomialAlg (p : ℕ) :
    LegendreSwapPolynomialRing p →ₐ[LegendreBase p] LegendreUniversalSwapRing p where
  __ := legendreSwapFromPolynomial p
  commutes' x := DFunLike.congr_fun (legendreSwapFromPolynomial_base p) x
/-- The presentation and its inverse cancel on the étale algebra. -/
theorem legendreSwapFromTo (p : ℕ) :
    (legendreSwapFromPolynomialAlg p).comp (legendreSwapToPolynomial p) =
      AlgHom.id (LegendreBase p) (LegendreUniversalSwapRing p) := by
  apply (quadraticEtalePair (-1 : (LegendreBase p)ˣ)).hom_ext
  change legendreSwapFromPolynomial p
    (legendreSwapToPolynomial p (quadraticEtalePair (-1 : (LegendreBase p)ˣ)).X) = _
  rw [legendreSwapToPolynomial_root, legendreSwapFromPolynomial_root]
  exact IsUnit.unit_spec _
/-- The inverse and presentation cancel on the Gaussian chart. -/
theorem legendreSwapToFrom (p : ℕ) :
    (legendreSwapToPolynomial p).comp (legendreSwapFromPolynomialAlg p) =
      AlgHom.id (LegendreBase p) (LegendreSwapPolynomialRing p) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (swapRootDenominator p))
  apply Polynomial.ringHom_ext'
  · apply Zsqrtd.hom_ext
    change legendreSwapToPolynomial p (legendreSwapFromPolynomial p (swapRoot p)) =
      swapRoot p
    rw [legendreSwapFromPolynomial_root, legendreSwapToPolynomial_unit]
  · change legendreSwapToPolynomial p
      (legendreSwapFromPolynomial p (swapRootParameter p)) = swapRootParameter p
    rw [legendreSwapFromPolynomial_parameter, AlgHom.commutes,
      legendreSwapPolynomialMap_parameter]
/-- The explicit two-sided presentation of the swap cover. -/
def legendreSwapPolynomialEquiv (p : ℕ) :
    LegendreUniversalSwapRing p ≃ₐ[LegendreBase p] LegendreSwapPolynomialRing p :=
  AlgEquiv.ofAlgHom (legendreSwapToPolynomial p) (legendreSwapFromPolynomialAlg p)
    (legendreSwapToFrom p) (legendreSwapFromTo p)
instance legendreUniversalSwapDomain (p : ℕ) [NeZero p] :
    IsDomain (LegendreUniversalSwapRing p) :=
  (legendreSwapPolynomialEquiv p).toMulEquiv.isDomain (LegendreSwapPolynomialRing p)
instance legendreUniversalSwapNoetherian (p : ℕ) :
    IsNoetherianRing (LegendreUniversalSwapRing p) :=
  isNoetherianRing_of_ringEquiv (LegendreSwapPolynomialRing p)
    (legendreSwapPolynomialEquiv p).symm.toRingEquiv

instance legendreUniversalSwapLevelUnit (p : ℕ) :
    Fact (IsUnit (p : LegendreUniversalSwapRing p)) := by
  constructor
  simpa only [map_natCast] using (legendreBase_units p).2.1.map
    (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p))
/-- The Legendre parameter pulled back to the actual swap cover. -/
def legendreSwapLiftedParameter (p : ℕ) : LegendreUniversalSwapRing p :=
  algebraMap (LegendreBase p) (LegendreUniversalSwapRing p) (legendreParameter p)
instance legendreSwapLiftedElliptic (p : ℕ) :
    (legendreCurve (legendreSwapLiftedParameter p)).IsElliptic := by
  dsimp only [legendreSwapLiftedParameter]
  rw [← legendreCurve_map]
  have : (legendreCurve (legendreParameter p)).IsElliptic := legendreModelElliptic p
  infer_instance
instance legendreSwapLiftedSwapElliptic (p : ℕ) :
    (legendreCurve (1 - legendreSwapLiftedParameter p)).IsElliptic := by
  change (legendreCurve (1 -
    algebraMap (LegendreBase p) (LegendreUniversalSwapRing p) (legendreParameter p))).IsElliptic
  rw [← map_one (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p)), ← map_sub,
    ← legendreCurve_map]
  infer_instance
/-- The actual cyclic swap transport on the universal root cover. -/
def legendreUniversalSwapCyclicIso (p : ℕ) [NeZero p] :
    scalarQuotientModel (legendreCurve (1 - legendreSwapLiftedParameter p)) p ≅
      scalarQuotientModel (legendreCurve (legendreSwapLiftedParameter p)) p :=
  legendreSwapCyclicParameterIso p (legendreSwapLiftedParameter p)
    (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ)) (legendreSwapRoot_square p)
/-- The cyclic swap transport is independent of root sign. -/
theorem legendreUniversalSwapCyclicIso_neg (p : ℕ) [Fact p.Prime] [NeZero p] :
    legendreSwapCyclicParameterIso p (legendreSwapLiftedParameter p)
        (-(quadraticEtaleUnit (-1 : (LegendreBase p)ˣ)))
        (by simpa only [Units.val_neg, neg_sq] using legendreSwapRoot_square p) =
      legendreUniversalSwapCyclicIso p :=
  legendreSwapCyclicParameterIso_neg p (legendreSwapLiftedParameter p)
    (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ)) (legendreSwapRoot_square p)

end WeierstrassCurve.CubicCharts

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendreParameterSymmetries
public import FLT.EllipticCurve.CubicCyclicSign

/-! # The integral reciprocal square-root cover

The standard étale cover adjoining a square root of the universal
Legendre parameter is explicitly isomorphic, over the Legendre base,
to ℤ[t, 1/(2pt(t²-1))], with λ mapped to t². The inverse maps prove
that this actual cover is a noetherian domain for nonzero level.
At invertible prime level it therefore carries the already constructed
cyclic reciprocal transport, with its square-root sign independence.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts

private theorem quadraticDerivative {R : Type*} [CommRing R] (d : Rˣ) :
    (quadraticRootPolynomial d).derivative = 2 * X := by
  simp [quadraticRootPolynomial]
  ring

/-- The product inverted in the polynomial presentation of the reciprocal cover. -/
def reciprocalRootDenominator (p : ℕ) : ℤ[X] := 2 * (p : ℤ[X]) * X * (X ^ 2 - 1)
/-- The localized polynomial presentation with λ equal to t². -/
abbrev LegendreReciprocalPolynomialRing (p : ℕ) := Localization.Away (reciprocalRootDenominator p)

instance legendreReciprocalPolynomialDomain (p : ℕ) [NeZero p] :
    IsDomain (LegendreReciprocalPolynomialRing p) :=
  Localization.Away.isDomain (by
    dsimp [reciprocalRootDenominator]
    apply mul_ne_zero
    · exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast NeZero.ne p)) X_ne_zero
    · intro h
      have hh := congrArg (fun q : ℤ[X] => q.eval 0) h
      norm_num at hh)

/-- The polynomial coordinate representing the square root of λ. -/
def reciprocalRootParameter (p : ℕ) : LegendreReciprocalPolynomialRing p :=
  algebraMap ℤ[X] (LegendreReciprocalPolynomialRing p) X

/-- The factors in the reciprocal-cover denominator are units. -/
theorem reciprocalRootParameter_units (p : ℕ) :
    IsUnit (2 : LegendreReciprocalPolynomialRing p) ∧
      IsUnit (p : LegendreReciprocalPolynomialRing p) ∧
      IsUnit (reciprocalRootParameter p) ∧ IsUnit (reciprocalRootParameter p ^ 2 - 1) := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := LegendreReciprocalPolynomialRing p) (reciprocalRootDenominator p)
  simpa only [reciprocalRootDenominator, map_mul, map_ofNat, map_natCast, map_sub,
    map_pow, map_one, reciprocalRootParameter, IsUnit.mul_iff, and_assoc] using h

/-- The Legendre base map sending λ to the square of the root parameter. -/
def legendreReciprocalPolynomialMap (p : ℕ) :
    LegendreBase p →+* LegendreReciprocalPolynomialRing p :=
  legendreSpecialize p (reciprocalRootParameter p ^ 2)
    (reciprocalRootParameter_units p).1 (reciprocalRootParameter_units p).2.1
    ((reciprocalRootParameter_units p).2.2.1.pow 2) (reciprocalRootParameter_units p).2.2.2

instance legendreReciprocalPolynomialAlgebra (p : ℕ) :
    Algebra (LegendreBase p) (LegendreReciprocalPolynomialRing p) :=
  (legendreReciprocalPolynomialMap p).toAlgebra

/-- The base parameter maps to t². -/
theorem legendreReciprocalPolynomialMap_parameter (p : ℕ) :
    algebraMap (LegendreBase p) (LegendreReciprocalPolynomialRing p) (legendreParameter p) =
      reciprocalRootParameter p ^ 2 :=
  legendreSpecialize_parameter p (reciprocalRootParameter p ^ 2)
    (reciprocalRootParameter_units p).1 (reciprocalRootParameter_units p).2.1
    ((reciprocalRootParameter_units p).2.2.1.pow 2) (reciprocalRootParameter_units p).2.2.2

/-- The actual standard étale square-root algebra over the universal Legendre chart. -/
abbrev LegendreUniversalReciprocalRing (p : ℕ) :=
  LegendreReciprocalRing (legendreParameterUnit p)

/-- The map from the actual reciprocal cover to its polynomial presentation. -/
def legendreReciprocalToPolynomial (p : ℕ) :
    LegendreUniversalReciprocalRing p →ₐ[LegendreBase p] LegendreReciprocalPolynomialRing p :=
  (quadraticEtalePair (legendreParameterUnit p)).lift (reciprocalRootParameter p) (by
    constructor
    · change aeval (reciprocalRootParameter p)
        (X ^ 2 - C (legendreParameterUnit p : LegendreBase p)) = 0
      rw [map_sub, map_pow, aeval_X, aeval_C, legendreParameterUnit_val,
        legendreReciprocalPolynomialMap_parameter, sub_self]
    · have hd := quadraticDerivative (legendreParameterUnit p)
      change IsUnit (aeval (reciprocalRootParameter p)
        (quadraticRootPolynomial (legendreParameterUnit p)).derivative)
      rw [hd, map_mul, map_ofNat, aeval_X]
      exact (reciprocalRootParameter_units p).1.mul (reciprocalRootParameter_units p).2.2.1)

/-- The distinguished root maps to the polynomial parameter. -/
theorem legendreReciprocalToPolynomial_root (p : ℕ) :
    legendreReciprocalToPolynomial p (quadraticEtalePair (legendreParameterUnit p)).X =
      reciprocalRootParameter p :=
  StandardEtalePair.lift_X _ _ _

/-- The distinguished root unit maps to the polynomial parameter. -/
theorem legendreReciprocalToPolynomial_unit (p : ℕ) :
    legendreReciprocalToPolynomial p
        (quadraticEtaleUnit (legendreParameterUnit p) : LegendreUniversalReciprocalRing p) =
      reciprocalRootParameter p := by
  simpa only [quadraticEtaleUnit, IsUnit.unit_spec] using legendreReciprocalToPolynomial_root p

/-- The distinguished root squares to the pulled-back Legendre parameter. -/
theorem legendreReciprocalRoot_square (p : ℕ) :
    (quadraticEtaleUnit (legendreParameterUnit p) : LegendreUniversalReciprocalRing p) ^ 2 =
      algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p) (legendreParameter p) := by
  simpa only [legendreParameterUnit_val] using quadraticEtaleUnit_square (legendreParameterUnit p)

/-- The actual reciprocal cover inverts the polynomial denominator factors. -/
theorem legendreReciprocalRoot_units (p : ℕ) :
    IsUnit (2 : LegendreUniversalReciprocalRing p) ∧
      IsUnit (p : LegendreUniversalReciprocalRing p) ∧
      IsUnit (quadraticEtaleUnit (legendreParameterUnit p) : LegendreUniversalReciprocalRing p) ∧
      IsUnit ((quadraticEtaleUnit (legendreParameterUnit p) :
        LegendreUniversalReciprocalRing p) ^ 2 - 1) := by
  let f := algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p)
  refine ⟨?_, ?_, (quadraticEtaleUnit (legendreParameterUnit p)).isUnit, ?_⟩
  · simpa only [map_ofNat] using (legendreBase_units p).1.map f
  · simpa only [map_natCast] using (legendreBase_units p).2.1.map f
  · rw [legendreReciprocalRoot_square]
    simpa only [map_sub, map_one] using (legendreBase_units p).2.2.2.map f

/-- The inverse presentation map obtained by evaluating at the distinguished root. -/
def legendreReciprocalFromPolynomial (p : ℕ) :
    LegendreReciprocalPolynomialRing p →+* LegendreUniversalReciprocalRing p :=
  IsLocalization.Away.lift (reciprocalRootDenominator p)
    (show IsUnit ((eval₂RingHom (Int.castRingHom (LegendreUniversalReciprocalRing p))
      (quadraticEtaleUnit (legendreParameterUnit p) : LegendreUniversalReciprocalRing p))
        (reciprocalRootDenominator p)) by
      simpa [reciprocalRootDenominator] using
        (((legendreReciprocalRoot_units p).1.mul (legendreReciprocalRoot_units p).2.1).mul
          (legendreReciprocalRoot_units p).2.2.1).mul (legendreReciprocalRoot_units p).2.2.2)

/-- Evaluation sends t to the distinguished root unit. -/
theorem legendreReciprocalFromPolynomial_parameter (p : ℕ) :
    legendreReciprocalFromPolynomial p (reciprocalRootParameter p) =
      (quadraticEtaleUnit (legendreParameterUnit p) : LegendreUniversalReciprocalRing p) := by
  change ((legendreReciprocalFromPolynomial p).comp
    (algebraMap ℤ[X] (LegendreReciprocalPolynomialRing p))) X = _
  rw [legendreReciprocalFromPolynomial, IsLocalization.Away.lift_comp]
  simp

/-- The inverse presentation map respects the Legendre coefficient map. -/
theorem legendreReciprocalFromPolynomial_base (p : ℕ) :
    (legendreReciprocalFromPolynomial p).comp
        (algebraMap (LegendreBase p) (LegendreReciprocalPolynomialRing p)) =
      algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p) := by
  apply legendreRingHom_ext p
  rw [RingHom.comp_apply, legendreReciprocalPolynomialMap_parameter, map_pow,
    legendreReciprocalFromPolynomial_parameter, legendreReciprocalRoot_square]

/-- The inverse presentation map as an algebra map over the Legendre base. -/
def legendreReciprocalFromPolynomialAlg (p : ℕ) :
    LegendreReciprocalPolynomialRing p →ₐ[LegendreBase p] LegendreUniversalReciprocalRing p where
  __ := legendreReciprocalFromPolynomial p
  commutes' x := DFunLike.congr_fun (legendreReciprocalFromPolynomial_base p) x

/-- The presentation followed by evaluation is the identity on the root algebra. -/
theorem legendreReciprocalFromTo (p : ℕ) :
    (legendreReciprocalFromPolynomialAlg p).comp (legendreReciprocalToPolynomial p) =
      AlgHom.id (LegendreBase p) (LegendreUniversalReciprocalRing p) := by
  apply (quadraticEtalePair (legendreParameterUnit p)).hom_ext
  change legendreReciprocalFromPolynomial p
    (legendreReciprocalToPolynomial p (quadraticEtalePair (legendreParameterUnit p)).X) = _
  rw [legendreReciprocalToPolynomial_root, legendreReciprocalFromPolynomial_parameter]
  exact IsUnit.unit_spec _

/-- Evaluation followed by the presentation is the identity on the polynomial chart. -/
theorem legendreReciprocalToFrom (p : ℕ) :
    (legendreReciprocalToPolynomial p).comp (legendreReciprocalFromPolynomialAlg p) =
      AlgHom.id (LegendreBase p) (LegendreReciprocalPolynomialRing p) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (reciprocalRootDenominator p))
  apply Polynomial.ringHom_ext'
  · exact Subsingleton.elim _ _
  · change legendreReciprocalToPolynomial p
      (legendreReciprocalFromPolynomial p (reciprocalRootParameter p)) = reciprocalRootParameter p
    rw [legendreReciprocalFromPolynomial_parameter, legendreReciprocalToPolynomial_unit]

/-- The explicit two-sided presentation of the actual reciprocal root cover. -/
def legendreReciprocalPolynomialEquiv (p : ℕ) :
    LegendreUniversalReciprocalRing p ≃ₐ[LegendreBase p] LegendreReciprocalPolynomialRing p :=
  AlgEquiv.ofAlgHom (legendreReciprocalToPolynomial p) (legendreReciprocalFromPolynomialAlg p)
    (legendreReciprocalToFrom p) (legendreReciprocalFromTo p)


instance legendreUniversalReciprocalDomain (p : ℕ) [NeZero p] :
    IsDomain (LegendreUniversalReciprocalRing p) :=
  (legendreReciprocalPolynomialEquiv p).toMulEquiv.isDomain (LegendreReciprocalPolynomialRing p)

instance legendreUniversalReciprocalNoetherian (p : ℕ) :
    IsNoetherianRing (LegendreUniversalReciprocalRing p) :=
  isNoetherianRing_of_ringEquiv (LegendreReciprocalPolynomialRing p)
    (legendreReciprocalPolynomialEquiv p).symm.toRingEquiv


instance legendreUniversalReciprocalLevelUnit (p : ℕ) :
    Fact (IsUnit (p : LegendreUniversalReciprocalRing p)) :=
  ⟨(legendreReciprocalRoot_units p).2.1⟩

/-- The Legendre parameter as a unit on the actual reciprocal cover. -/
def legendreReciprocalLiftedParameter (p : ℕ) : (LegendreUniversalReciprocalRing p)ˣ :=
  Units.map (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p)).toMonoidHom
    (legendreParameterUnit p)

instance legendreReciprocalLiftedElliptic (p : ℕ) :
    (legendreCurve (legendreReciprocalLiftedParameter p :
      LegendreUniversalReciprocalRing p)).IsElliptic := by
  change (legendreCurve
    (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p)
      (legendreParameterUnit p : LegendreBase p))).IsElliptic
  rw [legendreParameterUnit_val, ← legendreCurve_map]
  have : (legendreCurve (legendreParameter p)).IsElliptic := legendreModelElliptic p
  infer_instance

instance legendreReciprocalLiftedInverseElliptic (p : ℕ) :
    (legendreCurve (((legendreReciprocalLiftedParameter p)⁻¹ :
      (LegendreUniversalReciprocalRing p)ˣ) : LegendreUniversalReciprocalRing p)).IsElliptic := by
  change (legendreCurve
    (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p)
      (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))).IsElliptic
  rw [← legendreCurve_map]
  infer_instance

/-- The root relation expressed using the lifted parameter unit. -/
theorem legendreReciprocalLiftedRoot_square (p : ℕ) :
    (quadraticEtaleUnit (legendreParameterUnit p) : LegendreUniversalReciprocalRing p) ^ 2 =
      (legendreReciprocalLiftedParameter p : LegendreUniversalReciprocalRing p) :=
  quadraticEtaleUnit_square (legendreParameterUnit p)

/-- The actual reciprocal cyclic transport on the universal root cover. -/
def legendreUniversalReciprocalCyclicIso (p : ℕ) [NeZero p] :
    scalarQuotientModel
        (legendreCurve (((legendreReciprocalLiftedParameter p)⁻¹ :
          (LegendreUniversalReciprocalRing p)ˣ) : LegendreUniversalReciprocalRing p)) p ≅
      scalarQuotientModel (legendreCurve (legendreReciprocalLiftedParameter p :
        LegendreUniversalReciprocalRing p)) p :=
  legendreReciprocalCyclicParameterIso p (legendreReciprocalLiftedParameter p)
    (quadraticEtaleUnit (legendreParameterUnit p))
    (legendreReciprocalLiftedRoot_square p)

/-- The universal reciprocal cyclic transport is independent of root sign. -/
theorem legendreUniversalReciprocalCyclicIso_neg (p : ℕ) [Fact p.Prime] [NeZero p] :
    legendreReciprocalCyclicParameterIso p (legendreReciprocalLiftedParameter p)
        (-(quadraticEtaleUnit (legendreParameterUnit p)))
        (by simpa only [Units.val_neg, neg_sq] using
          legendreReciprocalLiftedRoot_square p) =
      legendreUniversalReciprocalCyclicIso p :=
  legendreReciprocalCyclicParameterIso_neg p (legendreReciprocalLiftedParameter p)
    (quadraticEtaleUnit (legendreParameterUnit p))
    (legendreReciprocalLiftedRoot_square p)

end WeierstrassCurve.CubicCharts

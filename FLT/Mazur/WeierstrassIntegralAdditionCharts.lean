/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineProduct
public import FLT.Mazur.WeierstrassIntegralAdditionFormula
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Regular addition on the two integral nonvertical slope charts

Localizing the affine product at either slope denominator gives an actual map
from the cubic coordinate algebra. These maps require neither a field nor a
reduced base. They do not cover pairs involving infinity or opposite points.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve WeierstrassIntegralAddition

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- A slope satisfying the two polynomial relations defines a regular chart map. -/
def additionHom (f : AffineProduct W →ₐ[R] S) (l : S)
    (hl : l * (f (productX₁ W) - f (productX₂ W)) = f (productY₁ W) - f (productY₂ W))
    (hc : l * (f (productY₁ W) + f (productY₂ W) + algebraMap R S W.a₁ *
      f (productX₂ W) + algebraMap R S W.a₃) =
      f (productX₁ W) ^ 2 + f (productX₁ W) * f (productX₂ W) + f (productX₂ W) ^ 2 +
      algebraMap R S W.a₂ * (f (productX₁ W) + f (productX₂ W)) +
      algebraMap R S W.a₄ - algebraMap R S W.a₁ * f (productY₁ W)) :
    Coordinate W 2 →ₐ[R] S :=
  evaluation W 2 ![(W.map (algebraMap R S)).toAffine.addX
      (f (productX₁ W)) (f (productX₂ W)) l,
    (W.map (algebraMap R S)).toAffine.addY
      (f (productX₁ W)) (f (productX₂ W)) (f (productY₁ W)) l, 1]
    ((Projective.equation_some ..).mpr
      (equation_add_of_relations _ (productLeft_equation W f) hl hc)) rfl

/-- Denominator of the secant slope. -/
def secantDenominator : AffineProduct W := productX₁ W - productX₂ W

/-- The principal open of the affine product where the x-coordinates differ by a unit. -/
def SecantChart := Localization.Away (secantDenominator W)

instance : CommRing (SecantChart W) :=
  inferInstanceAs (CommRing (Localization.Away (secantDenominator W)))

instance : Algebra (AffineProduct W) (SecantChart W) :=
  inferInstanceAs (Algebra (AffineProduct W) (Localization.Away (secantDenominator W)))

instance : Algebra R (SecantChart W) :=
  inferInstanceAs (Algebra R (Localization.Away (secantDenominator W)))

instance : IsScalarTower R (AffineProduct W) (SecantChart W) :=
  inferInstanceAs (IsScalarTower R (AffineProduct W) (Localization.Away (secantDenominator W)))

instance : IsLocalization.Away (secantDenominator W) (SecantChart W) :=
  inferInstanceAs
    (IsLocalization.Away (secantDenominator W) (Localization.Away (secantDenominator W)))


/-- Restriction of product functions to the secant chart. -/
def secantRestriction : AffineProduct W →ₐ[R] SecantChart W :=
  IsScalarTower.toAlgHom R (AffineProduct W) (SecantChart W)

/-- Regular secant slope on its principal open. -/
def secantSlope : SecantChart W :=
  (secantRestriction W (productY₁ W) - secantRestriction W (productY₂ W)) *
    IsLocalization.Away.invSelf (secantDenominator W)

/-- The regular secant slope satisfies the line equation. -/
theorem secantSlope_relation :
    secantSlope W * (secantRestriction W (productX₁ W) -
      secantRestriction W (productX₂ W)) =
      secantRestriction W (productY₁ W) - secantRestriction W (productY₂ W) := by
  rw [secantSlope, mul_assoc, mul_comm (IsLocalization.Away.invSelf _)]
  have hi : secantRestriction W (secantDenominator W) *
      IsLocalization.Away.invSelf (secantDenominator W) = 1 :=
    IsLocalization.Away.mul_invSelf (secantDenominator W)
  conv_lhs at hi =>
    arg 1
    rw [secantDenominator, map_sub]
  rw [hi, mul_one]

/-- Addition on the integral secant chart, contravariantly on coordinate algebras. -/
def secantAddition : Coordinate W 2 →ₐ[R] SecantChart W :=
  additionHom W (secantRestriction W) (secantSlope W) (secantSlope_relation W)
    (secant_relation _ (productLeft_equation W _) (productRight_equation W _)
      (by
        have h := IsLocalization.Away.algebraMap_isUnit (secantDenominator W)
          (S := SecantChart W)
        change IsUnit (secantRestriction W (secantDenominator W)) at h
        simpa only [secantDenominator, map_sub] using h)
      (secantSlope_relation W))

/-- Denominator of the slope chart containing the nonvertical tangent locus. -/
def tangentDenominator : AffineProduct W :=
  productY₁ W + productY₂ W + productLeft W (algebraMap R (Coordinate W 2) W.a₁) * productX₂ W +
    productLeft W (algebraMap R (Coordinate W 2) W.a₃)

/-- Numerator of the slope chart containing the nonvertical tangent locus. -/
def tangentNumerator : AffineProduct W :=
  productX₁ W ^ 2 + productX₁ W * productX₂ W + productX₂ W ^ 2 +
    productLeft W (algebraMap R (Coordinate W 2) W.a₂) * (productX₁ W + productX₂ W) +
    productLeft W (algebraMap R (Coordinate W 2) W.a₄) -
    productLeft W (algebraMap R (Coordinate W 2) W.a₁) * productY₁ W

/-- The second principal slope open in the actual affine product. -/
def TangentChart := Localization.Away (tangentDenominator W)

instance : CommRing (TangentChart W) :=
  inferInstanceAs (CommRing (Localization.Away (tangentDenominator W)))

instance : Algebra (AffineProduct W) (TangentChart W) :=
  inferInstanceAs (Algebra (AffineProduct W) (Localization.Away (tangentDenominator W)))

instance : Algebra R (TangentChart W) :=
  inferInstanceAs (Algebra R (Localization.Away (tangentDenominator W)))

instance : IsScalarTower R (AffineProduct W) (TangentChart W) :=
  inferInstanceAs (IsScalarTower R (AffineProduct W) (Localization.Away (tangentDenominator W)))

instance : IsLocalization.Away (tangentDenominator W) (TangentChart W) :=
  inferInstanceAs
    (IsLocalization.Away (tangentDenominator W) (Localization.Away (tangentDenominator W)))


/-- Restriction of product functions to the second slope chart. -/
def tangentRestriction : AffineProduct W →ₐ[R] TangentChart W :=
  IsScalarTower.toAlgHom R (AffineProduct W) (TangentChart W)

/-- Regular slope on the second principal open. -/
def tangentSlope : TangentChart W :=
  tangentRestriction W (tangentNumerator W) *
    IsLocalization.Away.invSelf (tangentDenominator W)

/-- The second slope satisfies its defining denominator equation. -/
theorem tangentSlope_relation :
    tangentSlope W * tangentRestriction W (tangentDenominator W) =
      tangentRestriction W (tangentNumerator W) := by
  rw [tangentSlope, mul_assoc, mul_comm (IsLocalization.Away.invSelf _)]
  have hi : tangentRestriction W (tangentDenominator W) *
      IsLocalization.Away.invSelf (tangentDenominator W) = 1 :=
    IsLocalization.Away.mul_invSelf (tangentDenominator W)
  rw [hi, mul_one]

/-- The second denominator equation written in restricted coordinates. -/
theorem tangentSlope_coordinates :
    tangentSlope W * (tangentRestriction W (productY₁ W) +
      tangentRestriction W (productY₂ W) + algebraMap R (TangentChart W) W.a₁ *
      tangentRestriction W (productX₂ W) + algebraMap R (TangentChart W) W.a₃) =
      tangentRestriction W (productX₁ W) ^ 2 +
      tangentRestriction W (productX₁ W) * tangentRestriction W (productX₂ W) +
      tangentRestriction W (productX₂ W) ^ 2 + algebraMap R (TangentChart W) W.a₂ *
      (tangentRestriction W (productX₁ W) + tangentRestriction W (productX₂ W)) +
      algebraMap R (TangentChart W) W.a₄ -
      algebraMap R (TangentChart W) W.a₁ * tangentRestriction W (productY₁ W) := by
  simpa only [tangentDenominator, tangentNumerator, map_add, map_mul, map_pow,
    map_sub, AlgHom.commutes] using tangentSlope_relation W

/-- The regular slope on the second chart also satisfies the line equation. -/
theorem tangentSlope_line :
    tangentSlope W * (tangentRestriction W (productX₁ W) -
      tangentRestriction W (productX₂ W)) =
      tangentRestriction W (productY₁ W) - tangentRestriction W (productY₂ W) :=
  tangent_relation _ (productLeft_equation W _) (productRight_equation W _) (by
    have h := IsLocalization.Away.algebraMap_isUnit (tangentDenominator W)
      (S := TangentChart W)
    change IsUnit (tangentRestriction W (tangentDenominator W)) at h
    simpa only [tangentDenominator, map_add, map_mul, AlgHom.commutes,
      WeierstrassCurve.toAffine, map_a₁, map_a₃] using h) (tangentSlope_coordinates W)

/-- Addition on the integral tangent chart, contravariantly on coordinate algebras. -/
def tangentAddition : Coordinate W 2 →ₐ[R] TangentChart W :=
  additionHom W (tangentRestriction W) (tangentSlope W)
    (tangentSlope_line W) (tangentSlope_coordinates W)

/-- The regular secant map has the classical addition coordinates. -/
@[simp] theorem secantAddition_coord (i : Fin 3) :
    secantAddition W (coord W 2 i) =
      ![(W.map (algebraMap R (SecantChart W))).toAffine.addX
          (secantRestriction W (productX₁ W)) (secantRestriction W (productX₂ W)) (secantSlope W),
        (W.map (algebraMap R (SecantChart W))).toAffine.addY
          (secantRestriction W (productX₁ W)) (secantRestriction W (productX₂ W))
          (secantRestriction W (productY₁ W)) (secantSlope W), 1] i :=
  MvPolynomial.aeval_X _ _

/-- The regular second slope map has the classical addition coordinates. -/
@[simp] theorem tangentAddition_coord (i : Fin 3) :
    tangentAddition W (coord W 2 i) =
      ![(W.map (algebraMap R (TangentChart W))).toAffine.addX
          (tangentRestriction W (productX₁ W)) (tangentRestriction W (productX₂ W))
          (tangentSlope W),
        (W.map (algebraMap R (TangentChart W))).toAffine.addY
          (tangentRestriction W (productX₁ W)) (tangentRestriction W (productX₂ W))
          (tangentRestriction W (productY₁ W)) (tangentSlope W), 1] i :=
  MvPolynomial.aeval_X _ _

end FLT.Mazur.WeierstrassIntegralChart

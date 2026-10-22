/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalChordOutput
public import FLT.Mazur.WeierstrassIntegralZeroSection

/-!
# Zero-denominator reciprocal chord specializations are the original infinity point

The statements apply after every algebra map out of the genuine reciprocal
source. In particular, vanishing of the denominator need only hold after specialization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassIntegralAddition
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "T" => DividedReciprocalChordRing W s b3 b4 b6 a c
local notation "O" => DividedReciprocalChordOutputRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "v" => dividedReciprocalChordCoordinates W s b3 b4 b6 a c
local notation "m" => dividedReciprocalChordSlope W s b3 b4 b6 a c

/-- A zero divided tangent denominator forces zero reciprocal slope after any specialization. -/
theorem dividedReciprocalChordSpecialization_slope (f : T →ₐ[R] B)
    (hx : f (j (dividedTangentDenominator W s b3 b4 b6 a c)) = 0) : f m = 0 := by
  change f (algebraMap S T (dividedTangentDenominator W s b3 b4 b6 a c) *
    IsLocalization.Away.invSelf (dividedTangentNumerator W s b3 b4 b6 a c)) = 0
  change f (algebraMap S T (dividedTangentDenominator W s b3 b4 b6 a c)) = 0 at hx
  rw [map_mul, hx, zero_mul]

/-- Every such specialization has homogeneous coordinates exactly [0,-1,0]. -/
theorem dividedReciprocalChordSpecialization_coordinates (f : T →ₐ[R] B)
    (hx : f (j (dividedTangentDenominator W s b3 b4 b6 a c)) = 0) (i : Fin 3) :
    f (v i) = ![0, -1, 0] i := by
  have hm := dividedReciprocalChordSpecialization_slope W s b3 b4 b6 a c f hx
  fin_cases i <;>
    simp [dividedReciprocalChordCoordinates, reciprocalXYZ, reciprocalH, hm]

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (e : DividedReciprocalChordOutputRing W s b3 b4 b6 a c →ₐ[R] B)
local notation "fe" => e.comp (IsScalarTower.toAlgHom R T O)

/-- Normalization gives the actual original infinity evaluation on every coordinate. -/
theorem dividedReciprocalChordSpecialization_output
    (hx : fe (j (dividedTangentDenominator W s b3 b4 b6 a c)) = 0) :
    e.comp (dividedReciprocalChordOutput W s b3 b4 b6 a c h3 h4 h6) =
      WeierstrassIntegralChart.chartInfinityEvaluation W := by
  have hv (i) : e (algebraMap T O (v i)) = ![0, -1, 0] i :=
    dividedReciprocalChordSpecialization_coordinates W s b3 b4 b6 a c fe hx i
  have hn := congrArg e (dividedReciprocalChordOutput_normalize W s b3 b4 b6 a c)
  simp only [map_mul, map_one, hv] at hn
  apply WeierstrassIntegralChart.hom_ext
  intro i
  simp only [AlgHom.comp_apply, dividedReciprocalChordOutput_coord, map_mul, hv]
  fin_cases i
  · simp
  · simpa [WeierstrassIntegralChart.chartInfinityEvaluation_coord] using hn
  · simp

/-- The normalized original curve output is its actual zero section over the same base. -/
theorem dividedReciprocalChordSpecialization_toCurve
    (hx : fe (j (dividedTangentDenominator W s b3 b4 b6 a c)) = 0) :
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        dividedReciprocalChordToCurve W s b3 b4 b6 a c h3 h4 h6 =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫
        WeierstrassIntegralChart.integralCurveZero W := by
  rw [dividedReciprocalChordToCurve, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (e.comp (dividedReciprocalChordOutput W s b3 b4 b6 a c h3 h4 h6)).toRingHom) ≫ _ = _
  rw [dividedReciprocalChordSpecialization_output W s b3 b4 b6 a c h3 h4 h6 e hx,
    WeierstrassIntegralChart.chartInfinityEvaluation_base,
    WeierstrassIntegralChart.integralCurveZero, ← Category.assoc, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassDilatation

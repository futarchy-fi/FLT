/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalChordTangentScheme
public import FLT.Mazur.WeierstrassDividedTangentSecantScheme

/-!
# The reciprocal chord/secant overlap factors through the tangent source

The divided equation difference forces the tangent denominator to be a unit
whenever both the divided numerator and secant denominator are units. This
holds over arbitrary rings and retains nilpotents.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "num" => dividedTangentNumerator W s b3 b4 b6 a c
local notation "den" => dividedTangentDenominator W s b3 b4 b6 a c
local notation "dx" => a (x W s b3 b4 b6) - c (x W s b3 b4 b6)
local notation "dy" => a (y W s b3 b4 b6) - c (y W s b3 b4 b6)

/-- The tangent denominator is a unit on the actual reciprocal chord/secant overlap. -/
theorem dividedReciprocalChordSecant_denominator_isUnit (f : S →ₐ[R] B)
    (hn : IsUnit (f num)) (hx : IsUnit (f dx)) : IsUnit (f den) := by
  have he := divided_equation_difference (W.map (algebraMap R B))
    (algebraMap R B s) (algebraMap R B b3) (algebraMap R B b4) (algebraMap R B b6)
    (equation_map W s b3 b4 b6 (f.comp a)) (equation_map W s b3 b4 b6 (f.comp c))
  have hprod : f den * f dy = f dx * f num := by
    simpa only [dividedTangentDenominator, dividedTangentNumerator,
      map_add, map_sub, map_mul, map_pow, AlgHom.commutes, AlgHom.comp_apply,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂] using he
  exact isUnit_of_mul_isUnit_left (hprod.symm ▸ hx.mul hn)

local notation "Q" => DividedReciprocalChordRing W s b3 b4 b6 a c
local notation "C" => DividedReciprocalChordOutputRing W s b3 b4 b6 a c
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "V" => DividedSecantRing W s b3 b4 b6 a c
local notation "jc" => (IsScalarTower.toAlgHom R Q C).comp (IsScalarTower.toAlgHom R S Q)
local notation "jv" => IsScalarTower.toAlgHom R S V
local notation "jt" => IsScalarTower.toAlgHom R S T
variable (e : DividedReciprocalChordOutputRing W s b3 b4 b6 a c →ₐ[R] B)
  (f : DividedSecantRing W s b3 b4 b6 a c →ₐ[R] B)
  (h : e.comp ((IsScalarTower.toAlgHom R
    (DividedReciprocalChordRing W s b3 b4 b6 a c)
    (DividedReciprocalChordOutputRing W s b3 b4 b6 a c)).comp
      (IsScalarTower.toAlgHom R S (DividedReciprocalChordRing W s b3 b4 b6 a c))) =
        f.comp (IsScalarTower.toAlgHom R S (DividedSecantRing W s b3 b4 b6 a c)))

include h in
/-- Both actual localization maps force the tangent denominator to be invertible. -/
theorem dividedReciprocalChordSecant_common_unit : IsUnit ((e.comp jc) den) := by
  apply dividedReciprocalChordSecant_denominator_isUnit W s b3 b4 b6 a c
  · exact (IsLocalization.Away.algebraMap_isUnit (S := Q) num).map
      (e.comp (IsScalarTower.toAlgHom R Q C))
  · rw [h]
    exact (IsLocalization.Away.algebraMap_isUnit (S := V) dx).map f

/-- The common overlap has an actual map from the tangent localization. -/
def dividedReciprocalChordSecantTangentLift : T →ₐ[R] B :=
  IsLocalization.Away.liftAlgHom den
    (dividedReciprocalChordSecant_common_unit W s b3 b4 b6 a c e f h)

/-- The lift preserves the whole input algebra, before taking any residue field. -/
theorem dividedReciprocalChordSecantTangentLift_source :
    (dividedReciprocalChordSecantTangentLift W s b3 b4 b6 a c e f h).comp jt = e.comp jc := by
  ext z
  change (IsLocalization.Away.lift den
    (dividedReciprocalChordSecant_common_unit W s b3 b4 b6 a c e f h) : T →+* B)
      (algebraMap S T z) = (e.comp jc) z
  exact IsLocalization.Away.lift_eq den
    (dividedReciprocalChordSecant_common_unit W s b3 b4 b6 a c e f h) z


end FLT.Mazur.WeierstrassDilatation

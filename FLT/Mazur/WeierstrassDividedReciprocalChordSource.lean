/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentSource
public import FLT.Mazur.WeierstrassDividedReciprocalFormula

/-!
# Reciprocal chords on the divided numerator open

Inverting the divided chord numerator constructs a reciprocal slope even
when the ordinate difference and tangent denominator both vanish. The full
input equations give both relations and an actual homogeneous cubic output.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassIntegralAddition
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "num" => dividedTangentNumerator W s b3 b4 b6 a c
local notation "den" => dividedTangentDenominator W s b3 b4 b6 a c

/-- The actual principal open of the divided chord numerator. -/
def DividedReciprocalChordRing := Localization.Away (dividedTangentNumerator W s b3 b4 b6 a c)
local notation "T" => DividedReciprocalChordRing W s b3 b4 b6 a c

instance dividedReciprocalChordCommRing : CommRing T :=
  inferInstanceAs (CommRing (Localization.Away num))
instance dividedReciprocalChordAlgebraSource : Algebra S T :=
  inferInstanceAs (Algebra S (Localization.Away num))
instance dividedReciprocalChordAlgebra : Algebra R T :=
  inferInstanceAs (Algebra R (Localization.Away num))
instance dividedReciprocalChordTower : IsScalarTower R S T :=
  inferInstanceAs (IsScalarTower R S (Localization.Away num))
instance dividedReciprocalChordLocalization : IsLocalization.Away num T :=
  inferInstanceAs (IsLocalization.Away num (Localization.Away num))
attribute [irreducible] DividedReciprocalChordRing

local notation "j" => IsScalarTower.toAlgHom R S T
local notation "u₁" => ((j).comp a) (x W s b3 b4 b6)
local notation "u₂" => ((j).comp c) (x W s b3 b4 b6)
local notation "v₁" => ((j).comp a) (y W s b3 b4 b6)
local notation "v₂" => ((j).comp c) (y W s b3 b4 b6)
local notation "q" => algebraMap R T s
local notation "W'" => W.map (algebraMap R T)

/-- The reciprocal chord slope uses the original divided numerator. -/
def dividedReciprocalChordSlope : T :=
  algebraMap S T den * IsLocalization.Away.invSelf num
local notation "m" => dividedReciprocalChordSlope W s b3 b4 b6 a c

/-- The reciprocal slope satisfies its defining chord relation. -/
theorem dividedReciprocalChordSlope_relation :
    m * algebraMap S T num = algebraMap S T den := by
  rw [dividedReciprocalChordSlope, mul_assoc, mul_comm (IsLocalization.Away.invSelf num),
    IsLocalization.Away.mul_invSelf, mul_one]

/-- The localized numerator is a unit without inverting the original scale. -/
theorem dividedReciprocalChord_numerator_isUnit :
    IsUnit (q * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2) + algebraMap R T W.a₂ * (u₁ + u₂) +
      algebraMap R T b4 - algebraMap R T W.a₁ * v₁) := by
  simpa only [dividedTangentNumerator, map_add, map_sub, map_mul, map_pow,
    ← IsScalarTower.algebraMap_apply R S T, AlgHom.comp_apply,
    IsScalarTower.coe_toAlgHom'] using (IsLocalization.Away.algebraMap_isUnit (S := T) num)

/-- The complete divided chord relation, before any specialization. -/
theorem dividedReciprocalChordSlope_chord :
    m * (q * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2) + algebraMap R T W.a₂ * (u₁ + u₂) +
      algebraMap R T b4 - algebraMap R T W.a₁ * v₁) =
        v₁ + v₂ + algebraMap R T W.a₁ * u₂ + algebraMap R T b3 := by
  simpa only [dividedTangentNumerator, dividedTangentDenominator, map_add, map_sub,
    map_mul, map_pow, ← IsScalarTower.algebraMap_apply R S T, AlgHom.comp_apply,
    IsScalarTower.coe_toAlgHom'] using
      dividedReciprocalChordSlope_relation W s b3 b4 b6 a c

/-- The two actual input equations imply the reciprocal line relation. -/
theorem dividedReciprocalChordSlope_line : m * (v₁ - v₂) = u₁ - u₂ := by
  apply (dividedReciprocalChord_numerator_isUnit W s b3 b4 b6 a c).mul_left_inj.mp
  have hc := dividedReciprocalChordSlope_chord W s b3 b4 b6 a c
  have he := divided_equation_difference W' q (algebraMap R T b3)
    (algebraMap R T b4) (algebraMap R T b6)
    (equation_map W s b3 b4 b6 ((j).comp a))
    (equation_map W s b3 b4 b6 ((j).comp c))
  simp only [map_a₁, map_a₂] at he
  linear_combination (v₁ - v₂) * hc + he

/-- Homogeneous original coordinates, including the missing vertical tangent output. -/
def dividedReciprocalChordCoordinates : Fin 3 → T :=
  reciprocalXYZ W' (q * u₁) (q * u₂) (q * v₁) m

/-- Vanishing tangent denominator gives the actual infinity coordinates. -/
theorem dividedReciprocalChordCoordinates_zero_den (hd : algebraMap S T den = 0) :
    dividedReciprocalChordCoordinates W s b3 b4 b6 a c = ![0, -1, 0] := by
  have hm : m = 0 := by rw [dividedReciprocalChordSlope, hd, zero_mul]
  rw [dividedReciprocalChordCoordinates, hm, reciprocalXYZ_zero]

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

include h3 h4 h6 in
/-- Both divided relations produce an output on the unchanged projective cubic. -/
theorem dividedReciprocalChordCoordinates_equation :
    (W').toProjective.Equation (dividedReciprocalChordCoordinates W s b3 b4 b6 a c) := by
  apply equation_reciprocalXYZ (y₂ := q * v₂)
  · rw [Affine.equation_iff]
    have he := equation_map W s b3 b4 b6 ((j).comp a)
    simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, h3, h4, h6, map_mul, map_pow]
    linear_combination q ^ 2 * he
  · linear_combination q * dividedReciprocalChordSlope_line W s b3 b4 b6 a c
  · have hc := dividedReciprocalChordSlope_chord W s b3 b4 b6 a c
    simp only [map_a₁, map_a₂, map_a₃, map_a₄, h3, h4, map_mul]
    linear_combination q * hc

end FLT.Mazur.WeierstrassDilatation

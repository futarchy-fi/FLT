/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalFormula
public import FLT.Mazur.WeierstrassDilatationCoefficients
public import FLT.Mazur.WeierstrassDilatationMorphism

/-!
# The actual divided reciprocal source

The ordinate difference defines a new principal open for two arbitrary
inputs. The constructed reciprocal slope satisfies both divided relations
and gives homogeneous coordinates on the unchanged original cubic.
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
local notation "dy" => a (y W s b3 b4 b6) - c (y W s b3 b4 b6)

/-- The genuine principal open where the divided ordinate difference is invertible. -/
def DividedReciprocalRing := Localization.Away (a (y W s b3 b4 b6) - c (y W s b3 b4 b6))
local notation "T" => DividedReciprocalRing W s b3 b4 b6 a c

instance dividedReciprocalCommRing : CommRing T :=
  inferInstanceAs (CommRing (Localization.Away dy))
instance dividedReciprocalAlgebraSource : Algebra S T :=
  inferInstanceAs (Algebra S (Localization.Away dy))
instance dividedReciprocalAlgebra : Algebra R T :=
  inferInstanceAs (Algebra R (Localization.Away dy))
instance dividedReciprocalTower : IsScalarTower R S T :=
  inferInstanceAs (IsScalarTower R S (Localization.Away dy))
instance dividedReciprocalLocalization : IsLocalization.Away dy T :=
  inferInstanceAs (IsLocalization.Away dy (Localization.Away dy))
attribute [irreducible] DividedReciprocalRing

local notation "j" => IsScalarTower.toAlgHom R S T
local notation "u₁" => ((j).comp a) (x W s b3 b4 b6)
local notation "u₂" => ((j).comp c) (x W s b3 b4 b6)
local notation "v₁" => ((j).comp a) (y W s b3 b4 b6)
local notation "v₂" => ((j).comp c) (y W s b3 b4 b6)
local notation "q" => algebraMap R T s
local notation "W'" => W.map (algebraMap R T)

/-- The reciprocal slope on the actual divided ordinate-difference open. -/
def dividedReciprocalSlope : T :=
  algebraMap S T (a (x W s b3 b4 b6) - c (x W s b3 b4 b6)) *
    IsLocalization.Away.invSelf dy
local notation "m" => dividedReciprocalSlope W s b3 b4 b6 a c

/-- The actual denominator is a unit without inverting the scale. -/
theorem dividedReciprocal_difference_isUnit : IsUnit (v₁ - v₂) := by
  simpa only [map_sub, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] using
    (IsLocalization.Away.algebraMap_isUnit (S := T) dy)

/-- The localized reciprocal slope satisfies the divided line relation. -/
theorem dividedReciprocalSlope_line : m * (v₁ - v₂) = u₁ - u₂ := by
  change m * (algebraMap S T (a (y W s b3 b4 b6)) -
    algebraMap S T (c (y W s b3 b4 b6))) = _
  rw [← map_sub, dividedReciprocalSlope, mul_assoc,
    mul_comm (IsLocalization.Away.invSelf dy), IsLocalization.Away.mul_invSelf, mul_one]
  simp only [map_sub, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']

/-- The divided equations give the reciprocal chord relation over the full new source. -/
theorem dividedReciprocalSlope_chord :
    m * (q * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2) + algebraMap R T W.a₂ * (u₁ + u₂) +
      algebraMap R T b4 - algebraMap R T W.a₁ * v₁) =
        v₁ + v₂ + algebraMap R T W.a₁ * u₂ + algebraMap R T b3 :=
  divided_reciprocal_relation (W') q (algebraMap R T b3) (algebraMap R T b4)
    (algebraMap R T b6) (equation_map W s b3 b4 b6 ((j).comp a))
    (equation_map W s b3 b4 b6 ((j).comp c))
    (dividedReciprocal_difference_isUnit W s b3 b4 b6 a c)
    (dividedReciprocalSlope_line W s b3 b4 b6 a c)

/-- Homogeneous coordinates of the actual original output, including infinity. -/
def dividedReciprocalCoordinates : Fin 3 → T :=
  reciprocalXYZ (W') (q * u₁) (q * u₂) (q * v₁) m

/-- Equal divided abscissae give the actual homogeneous infinity output on this source. -/
theorem dividedReciprocalCoordinates_equal_abscissa (hx : u₁ = u₂) :
    dividedReciprocalCoordinates W s b3 b4 b6 a c = ![0, -1, 0] :=
  (divided_reciprocal_equal_abscissa (W') q
    (dividedReciprocal_difference_isUnit W s b3 b4 b6 a c)
    (dividedReciprocalSlope_line W s b3 b4 b6 a c) hx).2

/-- Such pairs already have a unit output ordinate, so the infinity normalization is available. -/
theorem dividedReciprocalCoordinates_equal_abscissa_unit (hx : u₁ = u₂) :
    IsUnit (dividedReciprocalCoordinates W s b3 b4 b6 a c 1) := by
  rw [dividedReciprocalCoordinates_equal_abscissa W s b3 b4 b6 a c hx]
  exact isUnit_one.neg

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

include h3 h4 h6 in
/-- The constructed homogeneous output satisfies the unchanged original equation. -/
theorem dividedReciprocalCoordinates_equation :
    (W').toProjective.Equation (dividedReciprocalCoordinates W s b3 b4 b6 a c) := by
  dsimp only [dividedReciprocalCoordinates]
  apply divided_reciprocal_add_equation (W') q (algebraMap R T b3)
    (algebraMap R T b4) (algebraMap R T b6)
  · simp only [map_a₃, h3, map_mul]
  · simp only [map_a₄, h4, map_mul]
  · simp only [map_a₆, h6, map_mul, map_pow]
  · exact equation_map W s b3 b4 b6 ((j).comp a)
  · exact equation_map W s b3 b4 b6 ((j).comp c)
  · exact dividedReciprocal_difference_isUnit W s b3 b4 b6 a c
  · exact dividedReciprocalSlope_line W s b3 b4 b6 a c

end FLT.Mazur.WeierstrassDilatation

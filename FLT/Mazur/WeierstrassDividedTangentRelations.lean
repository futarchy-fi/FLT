/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentSource

/-!
# Tangent relations on arbitrary affine refinements

The localized denominator remains a unit after arbitrary base change. Both
line and chord relations hold without any regularity assumption on the scale.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (e : DividedTangentRing W s b3 b4 b6 a c →ₐ[R] B)
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "a'" => (e.comp j).comp a
local notation "c'" => (e.comp j).comp c
local notation "u₁" => a' (x W s b3 b4 b6)
local notation "u₂" => c' (x W s b3 b4 b6)
local notation "v₁" => a' (y W s b3 b4 b6)
local notation "v₂" => c' (y W s b3 b4 b6)
local notation "l" => e (dividedTangentSlope W s b3 b4 b6 a c)
local notation "q" => algebraMap R B s

/-- Every refinement retains the invertible second divided denominator. -/
theorem dividedTangentRefinement_denominator_isUnit :
    IsUnit (v₁ + v₂ + algebraMap R B W.a₁ * u₂ + algebraMap R B b3) := by
  have h := (IsLocalization.Away.algebraMap_isUnit
    (S := T) (dividedTangentDenominator W s b3 b4 b6 a c)).map e
  simpa only [dividedTangentDenominator, map_add, map_mul,
    ← IsScalarTower.algebraMap_apply R S T, AlgHom.commutes, AlgHom.comp_apply,
    IsScalarTower.coe_toAlgHom'] using h

/-- The constructed tangent slope retains its chord relation after any refinement. -/
theorem dividedTangentRefinement_chord :
    l * (v₁ + v₂ + algebraMap R B W.a₁ * u₂ + algebraMap R B b3) =
      q * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2) + algebraMap R B W.a₂ * (u₁ + u₂) +
        algebraMap R B b4 - algebraMap R B W.a₁ * v₁ := by
  have h := congrArg e (dividedTangentSlope_relation W s b3 b4 b6 a c)
  simpa only [dividedTangentDenominator, dividedTangentNumerator, map_add, map_mul,
    map_pow, map_sub, ← IsScalarTower.algebraMap_apply R S T, AlgHom.commutes,
    AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] using h

/-- The two divided equations give the line relation, including equal abscissae. -/
theorem dividedTangentRefinement_line : l * (u₁ - u₂) = v₁ - v₂ := by
  exact divided_tangent_relation (W.map (algebraMap R B)) q
    (algebraMap R B b3) (algebraMap R B b4) (algebraMap R B b6)
    (equation_map W s b3 b4 b6 a') (equation_map W s b3 b4 b6 c')
    (dividedTangentRefinement_denominator_isUnit W s b3 b4 b6 a c e)
    (dividedTangentRefinement_chord W s b3 b4 b6 a c e)

end FLT.Mazur.WeierstrassDilatation

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchEquation
public import FLT.Mazur.WeierstrassDividedTangentBranchSource

/-!
# A constructed divided output on the strict-branch tangent open

Under the indicated coefficient divisibilities, both output coordinates and
their divided equation are constructed on the genuine branch localization.
Only regularity of the coefficient scale is required; its image is not inverted.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "B" => DividedTangentBranchRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S B
local notation "u₁" => ((j).comp a) (x W s b3 b4 b6)
local notation "u₂" => ((j).comp c) (x W s b3 b4 b6)
local notation "v₁" => ((j).comp a) (y W s b3 b4 b6)
local notation "v₂" => ((j).comp c) (y W s b3 b4 b6)
local notation "q" => algebraMap R B s
local notation "W'" => W.map (algebraMap R B)
local notation "b3B" => algebraMap R B b3

/-- The two required branch inverses come from the actual source localization. -/
theorem dividedTangentBranch_coordinate_units :
    IsUnit (v₁ + (W').a₁ * u₁ + b3B) ∧
      IsUnit (v₁ + v₂ + (W').a₁ * u₂ + b3B) := by
  have h := (dividedTangentBranch_units W s b3 b4 b6 a c).symm
  simpa only [dividedTangentDenominator, dividedTangentBranchFactor,
    map_add, map_mul, map_a₁, ← IsScalarTower.algebraMap_apply R S B,
    AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] using h

variable (a2 b4' b6' : R)
local notation "a2B" => algebraMap R B a2
local notation "b4B" => algebraMap R B b4'
local notation "b6B" => algebraMap R B b6'

/-- The divided slope is constructed from the two localization inverses. -/
def dividedTangentBranchSlope : B :=
  tangentBranchSlope W' b3B a2B b4B b6B u₁ u₂ v₁ v₂
    (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).1
    (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).2

local notation "k" => dividedTangentBranchSlope W s b3 b4 b6 a c a2 b4' b6'

/-- The output abscissa in the divided target chart. -/
def dividedTangentBranchX : B := tangentBranchX W' q a2B u₁ u₂ k

/-- The output ordinate in the divided target chart. -/
def dividedTangentBranchY : B := tangentBranchY W' q b3B a2B u₁ u₂ v₁ k

variable [Module.Flat R S] (hs : IsRegular s)
  (h2 : W.a₂ = s * a2) (h3 : W.a₃ = s * b3)
  (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (h4' : b4 = s * b4') (h6' : b6 = s * b6')

include hs h2 h3 h4 h6 h4' h6' in
/-- The actual branch output satisfies the divided target equation. -/
theorem dividedTangentBranch_equation :
    let X := dividedTangentBranchX W s b3 b4 b6 a c a2 b4' b6'
    let Y := dividedTangentBranchY W s b3 b4 b6 a c a2 b4' b6'
    Y ^ 2 + (algebraMap R B W.a₁ * X + b3B) * Y =
      q * X ^ 3 + algebraMap R B W.a₂ * X ^ 2 + algebraMap R B b4 * X +
        algebraMap R B b6 := by
  apply tangentBranch_equation W' q b3B (algebraMap R B b4) (algebraMap R B b6)
    a2B b4B b6B u₁ u₂ v₁ v₂
    (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).1
    (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).2
    (dividedTangentBranch_scale_regular W s b3 b4 b6 a c hs)
  · simp only [map_a₂, h2, map_mul]
  · simp only [map_a₃, h3, map_mul]
  · simp only [map_a₄, h4, map_mul]
  · simp only [map_a₆, h6, map_mul, map_pow]
  · simp only [h4', map_mul]
  · simp only [h6', map_mul]
  · exact equation_map W s b3 b4 b6 ((j).comp a)
  · exact equation_map W s b3 b4 b6 ((j).comp c)

/-- The constructed algebra map lifts the output into the divided affine chart. -/
def dividedTangentBranchOutput : Coordinate W s b3 b4 b6 →ₐ[R] B :=
  evaluation W s b3 b4 b6
    (dividedTangentBranchX W s b3 b4 b6 a c a2 b4' b6')
    (dividedTangentBranchY W s b3 b4 b6 a c a2 b4' b6')
    (dividedTangentBranch_equation W s b3 b4 b6 a c a2 b4' b6' hs h2 h3 h4 h6 h4' h6')

/-- The first divided coordinate of the output is the explicit constructed abscissa. -/
theorem dividedTangentBranchOutput_x :
    dividedTangentBranchOutput W s b3 b4 b6 a c a2 b4' b6' hs h2 h3 h4 h6 h4' h6'
        (x W s b3 b4 b6) = dividedTangentBranchX W s b3 b4 b6 a c a2 b4' b6' :=
  evaluation_x ..

/-- The second divided coordinate of the output is the explicit constructed ordinate. -/
theorem dividedTangentBranchOutput_y :
    dividedTangentBranchOutput W s b3 b4 b6 a c a2 b4' b6' hs h2 h3 h4 h6 h4' h6'
        (y W s b3 b4 b6) = dividedTangentBranchY W s b3 b4 b6 a c a2 b4' b6' :=
  evaluation_y ..

end FLT.Mazur.WeierstrassDilatation

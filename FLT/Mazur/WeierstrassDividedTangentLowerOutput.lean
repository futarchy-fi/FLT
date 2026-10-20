/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentLowerEquation
public import FLT.Mazur.WeierstrassDividedTangentBranchOutput

/-!
# Actual strict-branch output in a smaller-scale chart

The two localization inverses construct the output coordinates. Flatness
preserves the regular target scale and hence the divided target equation.
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
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S) (t w a2 b4' b6' : R)
local notation "B" => DividedTangentBranchRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S B
local notation "u₁" => ((j).comp a) (x W s b3 b4 b6)
local notation "u₂" => ((j).comp c) (x W s b3 b4 b6)
local notation "v₁" => ((j).comp a) (y W s b3 b4 b6)
local notation "v₂" => ((j).comp c) (y W s b3 b4 b6)
local notation "W'" => W.map (algebraMap R B)
local notation "q" => algebraMap R B s
local notation "tB" => algebraMap R B t
local notation "wB" => algebraMap R B w
local notation "b3B" => algebraMap R B b3
local notation "a2B" => algebraMap R B a2
local notation "b4B" => algebraMap R B b4'
local notation "b6B" => algebraMap R B b6'

/-- The actual branch localization supplies the smaller-scale slope. -/
def dividedTangentLowerSlope : B :=
  tangentLowerSlope W' wB b3B a2B b4B b6B u₁ u₂ v₁ v₂
    (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).1
    (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).2
local notation "l" => dividedTangentLowerSlope W s b3 b4 b6 a c w a2 b4' b6'

/-- The constructed abscissa at the smaller output scale. -/
def dividedTangentLowerX : B := tangentLowerX W' tB wB a2B u₁ u₂ l

/-- The constructed ordinate at the smaller output scale. -/
def dividedTangentLowerY : B := tangentLowerY W' q tB wB b3B a2B u₁ u₂ v₁ l

variable [Module.Flat R S] (e3 e4 e6 : R) (ht : IsRegular t)
  (hs : s = t * w) (h2 : W.a₂ = t * a2)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (h4' : b4 = t * b4') (h6' : b6 = t * b6')
  (he3 : W.a₃ = t * e3) (he4 : W.a₄ = t * e4) (he6 : W.a₆ = t ^ 2 * e6)
local notation "X" => dividedTangentLowerX W s b3 b4 b6 a c t w a2 b4' b6'
local notation "Y" => dividedTangentLowerY W s b3 b4 b6 a c t w a2 b4' b6'

include ht hs h2 h3 h4 h6 h4' h6' he3 he4 he6 in
/-- Flatness and the original input equations prove the smaller-scale output equation. -/
theorem dividedTangentLower_equation :
    Y ^ 2 + (algebraMap R B W.a₁ * X + algebraMap R B e3) * Y =
      tB * X ^ 3 + algebraMap R B W.a₂ * X ^ 2 + algebraMap R B e4 * X +
        algebraMap R B e6 := by
  apply tangentLower_equation W' q tB wB b3B (algebraMap R B b4)
    (algebraMap R B b6) a2B b4B b6B
    (algebraMap R B e3) (algebraMap R B e4) (algebraMap R B e6) u₁ u₂ v₁ v₂
    (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).1
    (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).2
    (WeierstrassIntegralChart.flatRingHom_isRegular _
      (RingHom.flat_algebraMap_iff.mpr inferInstance) ht)
  · simp only [hs, map_mul]
  · simp only [map_a₂, h2, map_mul]
  · simp only [map_a₃, h3, map_mul]
  · simp only [map_a₄, h4, map_mul]
  · simp only [map_a₆, h6, map_mul, map_pow]
  · simp only [h4', map_mul]
  · simp only [h6', map_mul]
  · simp only [map_a₃, he3, map_mul]
  · simp only [map_a₄, he4, map_mul]
  · simp only [map_a₆, he6, map_mul, map_pow]
  · exact equation_map W s b3 b4 b6 ((j).comp a)
  · exact equation_map W s b3 b4 b6 ((j).comp c)

/-- The genuine algebra map into the supplied smaller-scale coordinate ring. -/
def dividedTangentLowerOutput : Coordinate W t e3 e4 e6 →ₐ[R] B :=
  evaluation W t e3 e4 e6 X Y
    (dividedTangentLower_equation W s b3 b4 b6 a c t w a2 b4' b6' e3 e4 e6
      ht hs h2 h3 h4 h6 h4' h6' he3 he4 he6)

/-- Evaluation of the new output on its abscissa generator. -/
theorem dividedTangentLowerOutput_x :
    dividedTangentLowerOutput W s b3 b4 b6 a c t w a2 b4' b6' e3 e4 e6
      ht hs h2 h3 h4 h6 h4' h6' he3 he4 he6 (x W t e3 e4 e6) = X := evaluation_x ..

/-- Evaluation of the new output on its ordinate generator. -/
theorem dividedTangentLowerOutput_y :
    dividedTangentLowerOutput W s b3 b4 b6 a c t w a2 b4' b6' e3 e4 e6
      ht hs h2 h3 h4 h6 h4' h6' he3 he4 he6 (y W t e3 e4 e6) = Y := evaluation_y ..

end FLT.Mazur.WeierstrassDilatation

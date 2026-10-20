/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentLowerOutput
public import FLT.Mazur.WeierstrassDividedTangentLowerResidueInput
public import FLT.Mazur.WeierstrassDividedVerticalSmooth

/-!
# Smoothness of the actual smaller-scale output map

The coefficient specialization theorem applies to the constructed algebra
map itself. Both input equations and branch inverses are supplied by the
original coordinate maps and the actual localization.
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

variable [Module.Flat R S] (e3 e4 e6 : R) (ht : IsRegular t)
  (hs : s = t * w) (h2 : W.a₂ = t * a2)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (h4' : b4 = t * b4') (h6' : b6 = t * b6')
  (he3 : W.a₃ = t * e3) (he4 : W.a₄ = t * e4) (he6 : W.a₆ = t ^ 2 * e6)
local notation "X" => dividedTangentLowerX W s b3 b4 b6 a c t w a2 b4' b6'
local notation "Y" => dividedTangentLowerY W s b3 b4 b6 a c t w a2 b4' b6'

local notation "out" => dividedTangentLowerOutput W s b3 b4 b6 a c t w a2 b4' b6'
  e3 e4 e6 ht hs h2 h3 h4 h6 h4' h6' he3 he4 he6

/-- Pulling back the vertical derivative evaluates it at the constructed coordinates. -/
theorem dividedTangentLowerOutput_vertical :
    out (verticalDerivative W t e3 e4 e6) = 2 * Y + (W').a₁ * X + algebraMap R B e3 := by
  rw [verticalDerivative_eq]
  simp only [map_add, map_mul, map_ofNat, AlgHom.commutes, map_a₁,
    dividedTangentLowerOutput_x, dividedTangentLowerOutput_y]

/-- The actual output is smooth at a terminal smaller-scale specialization. -/
theorem dividedTangentLowerOutput_specialized_vertical
    {K : Type*} [CommRing K] (f : B →+* K)
    (ht0 : f tB = 0) (hw0 : f wB = 0) (h30 : f b3B = 0)
    (h20 : f a2B = 0) (h40 : f b4B = 0) (he30 : f (algebraMap R B e3) = 0)
    (h60 : IsUnit (f b6B)) : IsUnit (f (out (verticalDerivative W t e3 e4 e6))) := by
  rw [dividedTangentLowerOutput_vertical]
  exact tangentLower_specialized_smooth f W' q tB wB b3B (algebraMap R B b4)
    (algebraMap R B b6) a2B b4B b6B u₁ u₂ v₁ v₂
    (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).1
    (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).2
    (by simp only [hs, map_mul]) (by simp only [map_a₂, h2, map_mul])
    (by simp only [h4', map_mul]) (by simp only [h6', map_mul])
    (equation_map W s b3 b4 b6 ((j).comp a))
    (equation_map W s b3 b4 b6 ((j).comp c))
    (algebraMap R B e3) ht0 hw0 h30 h20 h40 he30 h60

end FLT.Mazur.WeierstrassDilatation

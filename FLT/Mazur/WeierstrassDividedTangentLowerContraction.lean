/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentLowerOutput

/-!
# Smaller-scale branch outputs retain the actual tangent output

The constructed divided slope scales to the original localized slope. Both
output coordinates therefore contract to the unchanged tangent formula.
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
  (hs : s = t * w) (h2 : W.a₂ = t * a2)
  (h4' : b4 = t * b4') (h6' : b6 = t * b6')
local notation "B" => DividedTangentBranchRing W s b3 b4 b6 a c
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "e" => dividedTangentBranchRestriction W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S B
local notation "u₁" => ((j).comp a) (x W s b3 b4 b6)
local notation "u₂" => ((j).comp c) (x W s b3 b4 b6)
local notation "v₁" => ((j).comp a) (y W s b3 b4 b6)
local notation "v₂" => ((j).comp c) (y W s b3 b4 b6)
local notation "q" => algebraMap R B s
local notation "tB" => algebraMap R B t
local notation "wB" => algebraMap R B w
local notation "W'" => W.map (algebraMap R B)
local notation "k" => dividedTangentLowerSlope W s b3 b4 b6 a c w a2 b4' b6'

include hs h2 h4' h6' in
/-- The branch inverse construction recovers the actual original tangent slope. -/
theorem dividedTangentLowerSlope_scale :
    tB * k = e (dividedTangentSlope W s b3 b4 b6 a c) := by
  have hc := tangentLowerSlope_chord W' q tB wB (algebraMap R B b3)
    (algebraMap R B b4) (algebraMap R B b6) (algebraMap R B a2)
    (algebraMap R B b4') (algebraMap R B b6') u₁ u₂ v₁ v₂
    (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).1
    (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).2
    (by simp only [hs, map_mul]) (by simp only [map_a₂, h2, map_mul])
    (by simp only [h4', map_mul]) (by simp only [h6', map_mul])
    (equation_map W s b3 b4 b6 ((j).comp a))
  have h := congrArg e (dividedTangentSlope_relation W s b3 b4 b6 a c)
  simp only [map_mul, dividedTangentBranchRestriction_source] at h
  have h' : e (dividedTangentSlope W s b3 b4 b6 a c) *
      (v₁ + v₂ + (W').a₁ * u₂ + algebraMap R B b3) =
      q * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2) + (W').a₂ * (u₁ + u₂) +
        algebraMap R B b4 - (W').a₁ * v₁ := by
    simpa only [dividedTangentDenominator, dividedTangentNumerator, map_a₁, map_a₂,
      map_add, map_sub, map_mul, map_pow, ← IsScalarTower.algebraMap_apply R S B,
      AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] using h
  exact (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).2.mul_left_inj.mp
    (hc.trans h'.symm)

include hs h2 h4' h6' in
/-- The branch abscissa contracts to exactly the original tangent abscissa. -/
theorem dividedTangentLowerX_scale :
    tB * dividedTangentLowerX W s b3 b4 b6 a c t w a2 b4' b6' =
      e (dividedTangentX W s b3 b4 b6 a c) := by
  rw [dividedTangentLowerX, tangentLowerX_scale W' q tB wB (algebraMap R B a2)
    u₁ u₂ (by simp only [hs, map_mul]) (by simp only [map_a₂, h2, map_mul]),
    dividedTangentLowerSlope_scale W s b3 b4 b6 a c t w a2 b4' b6' hs h2 h4' h6']
  simp only [dividedTangentX, Affine.addX, map_sub, map_add, map_mul, map_pow,
    map_a₁, map_a₂, AlgHom.commutes, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
    dividedTangentBranchRestriction_source]

include hs h2 h4' h6' in
/-- The branch ordinate contracts to exactly the original tangent ordinate. -/
theorem dividedTangentLowerY_scale (h3 : W.a₃ = s * b3) :
    tB * dividedTangentLowerY W s b3 b4 b6 a c t w a2 b4' b6' =
      e (dividedTangentY W s b3 b4 b6 a c) := by
  rw [dividedTangentLowerY, tangentLowerY_scale W' q tB wB (algebraMap R B b3)
    (algebraMap R B a2) u₁ u₂ v₁ (by simp only [hs, map_mul])
    (by simp only [map_a₂, h2, map_mul])
    (by simp only [map_a₃, h3, map_mul]),
    dividedTangentLowerSlope_scale W s b3 b4 b6 a c t w a2 b4' b6' hs h2 h4' h6']
  simp only [dividedTangentY, Affine.addY, Affine.negY, Affine.negAddY, Affine.addX,
    map_sub, map_add, map_mul, map_pow, map_neg, map_a₁, map_a₂, map_a₃,
    AlgHom.commutes, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
    dividedTangentBranchRestriction_source]

end FLT.Mazur.WeierstrassDilatation

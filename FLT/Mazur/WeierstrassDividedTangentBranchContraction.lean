/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchOutput

/-!
# The branch lift retains the actual tangent output

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
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S) (a2 b4' b6' : R)
  (h2 : W.a₂ = s * a2) (h4' : b4 = s * b4') (h6' : b6 = s * b6')
local notation "B" => DividedTangentBranchRing W s b3 b4 b6 a c
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "e" => dividedTangentBranchRestriction W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S B
local notation "u₁" => ((j).comp a) (x W s b3 b4 b6)
local notation "u₂" => ((j).comp c) (x W s b3 b4 b6)
local notation "v₁" => ((j).comp a) (y W s b3 b4 b6)
local notation "v₂" => ((j).comp c) (y W s b3 b4 b6)
local notation "q" => algebraMap R B s
local notation "W'" => W.map (algebraMap R B)
local notation "k" => dividedTangentBranchSlope W s b3 b4 b6 a c a2 b4' b6'

include h2 h4' h6' in
/-- The branch inverse construction recovers the actual original tangent slope. -/
theorem dividedTangentBranchSlope_scale :
    q * k = e (dividedTangentSlope W s b3 b4 b6 a c) := by
  apply tangentBranchSlope_mul W' q (algebraMap R B b3) (algebraMap R B b4)
    (algebraMap R B b6) (algebraMap R B a2) (algebraMap R B b4') (algebraMap R B b6')
    u₁ u₂ v₁ v₂ (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).1
    (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).2
  · simp only [map_a₂, h2, map_mul]
  · simp only [h4', map_mul]
  · simp only [h6', map_mul]
  · exact equation_map W s b3 b4 b6 ((j).comp a)
  · have h := congrArg e (dividedTangentSlope_relation W s b3 b4 b6 a c)
    simp only [map_mul, dividedTangentBranchRestriction_source] at h
    simpa only [dividedTangentDenominator, dividedTangentNumerator, map_a₁, map_a₂,
      map_add, map_sub, map_mul, map_pow, ← IsScalarTower.algebraMap_apply R S B,
      AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] using h

include h2 h4' h6' in
/-- The branch abscissa contracts to exactly the original tangent abscissa. -/
theorem dividedTangentBranchX_scale :
    q * dividedTangentBranchX W s b3 b4 b6 a c a2 b4' b6' =
      e (dividedTangentX W s b3 b4 b6 a c) := by
  rw [dividedTangentBranchX, tangentBranchX_scale W' q (algebraMap R B a2)
    u₁ u₂ (by simp only [map_a₂, h2, map_mul]),
    dividedTangentBranchSlope_scale W s b3 b4 b6 a c a2 b4' b6' h2 h4' h6']
  simp only [dividedTangentX, Affine.addX, map_sub, map_add, map_mul, map_pow,
    map_a₁, map_a₂, AlgHom.commutes, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
    dividedTangentBranchRestriction_source]

include h2 h4' h6' in
/-- The branch ordinate contracts to exactly the original tangent ordinate. -/
theorem dividedTangentBranchY_scale (h3 : W.a₃ = s * b3) :
    q * dividedTangentBranchY W s b3 b4 b6 a c a2 b4' b6' =
      e (dividedTangentY W s b3 b4 b6 a c) := by
  rw [dividedTangentBranchY, tangentBranchY_scale W' q (algebraMap R B b3)
    (algebraMap R B a2) u₁ u₂ v₁ (by simp only [map_a₂, h2, map_mul])
    (by simp only [map_a₃, h3, map_mul]),
    dividedTangentBranchSlope_scale W s b3 b4 b6 a c a2 b4' b6' h2 h4' h6']
  simp only [dividedTangentY, Affine.addY, Affine.negY, Affine.negAddY, Affine.addX,
    map_sub, map_add, map_mul, map_pow, map_neg, map_a₁, map_a₂, map_a₃,
    AlgHom.commutes, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
    dividedTangentBranchRestriction_source]

end FLT.Mazur.WeierstrassDilatation

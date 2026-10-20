/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchDeeperEquation
public import FLT.Mazur.WeierstrassDividedTangentBranchSecondResidueUnit
public import FLT.Mazur.WeierstrassDividedTangentBranchMap

/-!
# Smoothness of the second output beyond quadruple depth

The second ordinate identity exposes a unit opposite branch factor.
When the second divided coefficients vanish, the actual output equation
forces its ordinate to vanish and its vertical derivative to be a unit.
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

variable (a2 b4' b6' : R)
  (h2 : W.a₂ = s * a2) (h4' : b4 = s * b4') (h6' : b6 = s * b6')

variable (b3' b6'' : R) (h3' : b3 = s * b3') (h6'' : b6' = s * b6'')
local notation "X" => dividedTangentBranchX W s b3 b4 b6 a c a2 b4' b6'
local notation "Y" => dividedTangentBranchY W s b3 b4 b6 a c a2 b4' b6'

local notation "X₂" => dividedTangentBranchDeeperX W s b3 b4 b6 a c a2 b4' b6'
  h2 h4' h6' b3' b6'' h3' h6''
local notation "Y₂" => dividedTangentBranchDeeperY W s b3 b4 b6 a c a2 b4' b6'
  h2 h4' h6' b3' b6'' h3' h6''
variable [Module.Flat R S] (hs : IsRegular s)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

local notation "hc" => (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).1
local notation "hd" => (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).2
local notation "t₁" => tangentBranchOrdinate W' b3B (algebraMap R B a2)
  (algebraMap R B b4') (algebraMap R B b6') u₁ v₁ hc
local notation "l" => dividedTangentBranchSlope W s b3 b4 b6 a c a2 b4' b6'

include hs in
/-- The second ordinate retains the exact quotient identity on the whole branch source. -/
theorem dividedTangentBranchDeeper_ordinate :
    Y₂ = -(q * l + algebraMap R B W.a₁) * X₂ + l * u₁ - t₁ -
      algebraMap R B b3' := by
  apply tangentBranch_second_ordinate W' b3B (algebraMap R B a2)
    (algebraMap R B b4') (algebraMap R B b6') u₁ u₂ v₁ v₂ hc hd q
    (algebraMap R B b3') X₂ Y₂
    (dividedTangentBranch_scale_regular W s b3 b4 b6 a c hs)
  · simp only [h3', map_mul]
  · exact dividedTangentBranchDeeperX_mul ..
  · exact dividedTangentBranchDeeperY_mul ..
  · apply tangentBranchOrdinate_mul W' q b3B (algebraMap R B b4)
      (algebraMap R B b6) (algebraMap R B a2) (algebraMap R B b4')
      (algebraMap R B b6') u₁ v₁ hc
    · simp only [map_a₂, h2, map_mul]
    · simp only [h4', map_mul]
    · simp only [h6', map_mul]
    · exact equation_map W s b3 b4 b6 ((j).comp a)

include hs h3 h4 h6 in
/-- Vanishing second coefficients give a unit vertical derivative of the actual second output. -/
theorem dividedTangentBranchDeeper_specialized_vertical
    {K : Type*} [CommRing K] (f : B →+* K) (hq : f q = 0)
    (hb3 : f (algebraMap R B b3') = 0) (hb4 : f (algebraMap R B b4') = 0)
    (hb6 : f (algebraMap R B b6'') = 0) :
    IsUnit (f (2 * Y₂ + algebraMap R B W.a₁ * X₂ + algebraMap R B b3')) := by
  have h30 : f b3B = 0 := by simp only [h3', map_mul, hq, zero_mul]
  have h60 : f (algebraMap R B b6') = 0 := by
    simp only [h6'', map_mul, hq, zero_mul]
  have h20 : f (algebraMap R B W.a₂) = 0 := by
    simp only [h2, map_mul, hq, zero_mul]
  have hv := dividedTangentBranch_specialFiber_ordinates W s b3 b4 b6 a c
    a2 b4' b6' h2 h4' h6' f hq
  have hc' : IsUnit (f v₁ + ((W').map f).a₁ * f u₁ + f b3B) := by
    simpa only [map_add, map_mul, map_a₁] using (hc).map f
  have hd' : IsUnit (f v₁ + f v₂ + ((W').map f).a₁ * f u₂ + f b3B) := by
    simpa only [map_add, map_mul, map_a₁] using (hd).map f
  have hu := tangentBranch_second_residue_unit ((W').map f) (f b3B)
    (f (algebraMap R B a2)) (f (algebraMap R B b4')) (f (algebraMap R B b6'))
    (f u₁) (f u₂) (f v₁) (f v₂) hc' hd' h30 hb4 h60 hv.1 hv.2
  rw [← tangentBranchSlope_map f W' b3B (algebraMap R B a2)
    (algebraMap R B b4') (algebraMap R B b6') u₁ u₂ v₁ v₂ hc hd hc' hd',
    ← tangentBranchOrdinate_map f W' b3B (algebraMap R B a2)
      (algebraMap R B b4') (algebraMap R B b6') u₁ v₁ hc hc'] at hu
  have hy := congrArg f (dividedTangentBranchDeeper_ordinate W s b3 b4 b6 a c
    a2 b4' b6' h2 h4' h6' b3' b6'' h3' h6'' hs)
  simp only [map_add, map_mul, map_sub, map_neg, hq, hb3, zero_mul,
    zero_add, sub_zero] at hy
  have hunit : IsUnit (f Y₂ + f (algebraMap R B W.a₁) * f X₂) := by
    have he : f Y₂ + f (algebraMap R B W.a₁) * f X₂ = f l * f u₁ - f t₁ := by
      linear_combination hy
    rw [he]
    exact hu
  have he := congrArg f (dividedTangentBranchDeeper_equation W s b3 b4 b6 a c
    a2 b4' b6' h2 h4' h6' b3' b6'' h3' h6'' hs h3 h4 h6)
  simp only [map_add, map_mul, map_pow, hq, h20, hb3, hb4, hb6, zero_pow (by decide : 2 ≠ 0),
    zero_mul, add_zero] at he
  simpa only [map_add, map_mul, map_ofNat, hb3, add_zero] using
    secondBranch_vertical_isUnit he hunit

end FLT.Mazur.WeierstrassDilatation

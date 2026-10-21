/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedUnequalSecantFormula
public import FLT.Mazur.WeierstrassDividedDepthMaps
public import FLT.Mazur.WeierstrassDividedSecantFlatSourceExt

/-!
# Explicit secants for inputs at different depths

Keep the right input at its own depth before contracting it to the left
depth. On the genuine secant localization, construct both output coordinates
divided by the depth-difference scale. No input derivative is assumed nonzero.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassCurve
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k l : ℕ}
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)

/-- The right input contracted to the left input's actual depth. -/
def unequalDepthRight : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S :=
  c.comp (depthTransition π k l hπ hkl W d.b3 d.b4 d.b6 e.b3 e.b4 e.b6
    d.factor3 d.factor4 d.factor6 e.factor3 e.factor4 e.factor6)

local notation "c₀" => unequalDepthRight hπ d e hkl c

/-- The contracted right abscissa has exactly the extra depth factor. -/
@[simp] theorem unequalDepthRight_x :
    c₀ (x W (π ^ k) d.b3 d.b4 d.b6) =
      algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6) := by
  simp only [unequalDepthRight, AlgHom.comp_apply, depthTransition_x, map_mul, AlgHom.commutes]

/-- The ordinate has the same factor, without restricting either input. -/
@[simp] theorem unequalDepthRight_y :
    c₀ (y W (π ^ k) d.b3 d.b4 d.b6) =
      algebraMap R S (π ^ (l - k)) * c (y W (π ^ l) e.b3 e.b4 e.b6) := by
  simp only [unequalDepthRight, AlgHom.comp_apply, depthTransition_y, map_mul, AlgHom.commutes]

/-- The actual open where the unequal-depth secant denominator is invertible. -/
abbrev UnequalDepthSecantRing := DividedSecantRing W (π ^ k) d.b3 d.b4 d.b6 a c₀

local notation "T" => UnequalDepthSecantRing hπ d e hkl a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "x₁" => ((j).comp a) (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "y₁" => ((j).comp a) (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "x₂" => ((j).comp c) (x W (π ^ l) e.b3 e.b4 e.b6)
local notation "y₂" => ((j).comp c) (y W (π ^ l) e.b3 e.b4 e.b6)
local notation "s" => algebraMap R T (π ^ k)
local notation "t" => algebraMap R T (π ^ (l - k))
local notation "dx" => a (x W (π ^ k) d.b3 d.b4 d.b6) - c₀ (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "i" => (IsLocalization.Away.invSelf dx : T)
local notation "slope" => dividedSecantSlope W (π ^ k) d.b3 d.b4 d.b6 a c₀
local notation "W'" => W.map (algebraMap R T)

/-- The depth-difference quotient of the original secant abscissa. -/
def unequalDepthSecantX : T :=
  unequalSecantX W' s t (algebraMap R T e.b3) (algebraMap R T e.b4)
    (algebraMap R T e.b6) x₁ y₁ x₂ y₂ i

/-- The depth-difference quotient of the original secant ordinate. -/
def unequalDepthSecantY : T :=
  unequalSecantY W' s t (algebraMap R T e.b3) (algebraMap R T e.b4)
    (algebraMap R T e.b6) x₁ y₁ x₂ y₂ i slope

/-- The inverse used in both quotients belongs to the original secant localization. -/
theorem unequalDepthSecant_inverse : i * (x₁ - t * x₂) = 1 := by
  have h := IsLocalization.Away.mul_invSelf (S := T) dx
  rw [mul_comm] at h
  simpa only [map_sub, unequalDepthRight_x, map_mul, AlgHom.comp_apply,
    IsScalarTower.coe_toAlgHom', ← IsScalarTower.algebraMap_apply R S T] using h

/-- The existing secant slope uses the uncontracted deeper input with its exact factor. -/
theorem unequalDepthSecant_chord : slope * (x₁ - t * x₂) = y₁ - t * y₂ := by
  have h := dividedSecantSlope_relation W (π ^ k) d.b3 d.b4 d.b6 a c₀
  simpa only [AlgHom.comp_apply, unequalDepthRight_x, unequalDepthRight_y, map_mul,
    IsScalarTower.coe_toAlgHom', ← IsScalarTower.algebraMap_apply R S T] using h

/-- The computed abscissa scales to the actual original secant output. -/
theorem unequalDepthSecantX_scale :
    t * unequalDepthSecantX hπ d e hkl a c =
      dividedSecantX W (π ^ k) d.b3 d.b4 d.b6 a c₀ := by
  have hpow : π ^ l = π ^ k * π ^ (l - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkl]
  have h₁ := equation_map W (π ^ k) d.b3 d.b4 d.b6 ((j).comp a)
  simp only [depth_coefficient_factor π k l hπ hkl d.factor3 e.factor3,
    depth_coefficient_factor π k l hπ hkl d.factor4 e.factor4,
    depth_constant_factor π k l hπ hkl d.factor6 e.factor6] at h₁
  have h₂ := equation_map W (π ^ l) e.b3 e.b4 e.b6 ((j).comp c)
  have h := unequalSecantX_scale W' s t (algebraMap R T e.b3)
    (algebraMap R T e.b4) (algebraMap R T e.b6) x₁ y₁ x₂ y₂ i slope
    (unequalDepthSecant_inverse hπ d e hkl a c)
    (unequalDepthSecant_chord hπ d e hkl a c)
    (by simpa only [map_a₁, map_a₂, map_mul, map_pow] using h₁)
    (by simpa only [map_a₁, map_a₂, hpow, map_mul] using h₂)
  simpa only [unequalDepthSecantX, dividedSecantX, AlgHom.comp_apply,
    unequalDepthRight_x, map_mul, IsScalarTower.coe_toAlgHom',
    ← IsScalarTower.algebraMap_apply R S T] using h

/-- The computed ordinate scales to the same original secant output. -/
theorem unequalDepthSecantY_scale :
    t * unequalDepthSecantY hπ d e hkl a c =
      dividedSecantY W (π ^ k) d.b3 d.b4 d.b6 a c₀ := by
  have h3 : W.a₃ = π ^ k * π ^ (l - k) * e.b3 := by
    rw [← pow_add, Nat.add_sub_of_le hkl]
    exact e.factor3
  have hx := unequalDepthSecantX_scale hπ d e hkl a c
  have h := unequalSecantY_scale W' s t (algebraMap R T e.b3)
    (algebraMap R T e.b4) (algebraMap R T e.b6) x₁ y₁ x₂ y₂ i slope
    (unequalDepthSecant_inverse hπ d e hkl a c)
    (unequalDepthSecant_chord hπ d e hkl a c)
    (by simp only [map_a₃, h3, map_mul])
    (by simpa only [unequalDepthSecantX, dividedSecantX, AlgHom.comp_apply,
          unequalDepthRight_x, map_mul, IsScalarTower.coe_toAlgHom',
          ← IsScalarTower.algebraMap_apply R S T] using hx)
  simpa only [unequalDepthSecantY, dividedSecantY, AlgHom.comp_apply,
    unequalDepthRight_x, map_mul, IsScalarTower.coe_toAlgHom',
    ← IsScalarTower.algebraMap_apply R S T] using h

end FLT.Mazur.WeierstrassDividedDepth

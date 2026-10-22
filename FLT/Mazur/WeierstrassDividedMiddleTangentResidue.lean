/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentPrimeSmooth
public import FLT.Mazur.WeierstrassDividedUnequalDepthMiddleCoverage

/-!
# Tangent output abscissae at exact middle depth

The terminal constant is a unit. Both input equations and the actual tangent
chord relation force the slope and its translate by a₁ to be units. Their
product is the original output abscissa, even when either input abscissa is zero.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing WeierstrassCurve
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S K : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  [CommRing S] [Algebra R S] [CommRing K] [Algebra R K]
  {W : WeierstrassCurve R} {π : R} {k depth : ℕ}
  (node : SplitNodeDepth W π depth) (d : Data W π k)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "T" => DividedTangentRing W (π ^ k) d.b3 d.b4 d.b6 a c
variable (e : DividedTangentRing W (π ^ k) d.b3 d.b4 d.b6 a c →ₐ[R] K)
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "a'" => (e.comp j).comp a
local notation "c'" => (e.comp j).comp c
local notation "u₁" => a' (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "u₂" => c' (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "v₁" => a' (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "v₂" => c' (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "α" => algebraMap R K W.a₁
local notation "l" => e (dividedTangentSlope W (π ^ k) d.b3 d.b4 d.b6 a c)

include node d a c

/-- Every middle-depth tangent output has invertible original abscissa. -/
theorem middleTangentOutput_x_isUnit (hk : 0 < k) (hm : 2 * k = depth)
    (hp : algebraMap R K π = 0) :
    IsUnit (e (dividedTangentX W (π ^ k) d.b3 d.b4 d.b6 a c)) := by
  have van (b : R) (hb : b ∈ maximalIdeal R) : algebraMap R K b = 0 := by
    rw [node.maximalIdeal_eq, Ideal.mem_span_singleton] at hb
    obtain ⟨v, rfl⟩ := hb
    rw [map_mul, hp, zero_mul]
  have hs : algebraMap R K (π ^ k) = 0 := by
    rw [map_pow, hp, zero_pow (by omega)]
  have hlin := divided_linear_deep_mem node d (by omega : k ≤ depth + 1)
  have h3 := van d.b3 (Ideal.pow_le_self (by omega) hlin.1)
  have h4 := van d.b4 (Ideal.pow_le_self (by omega) hlin.2)
  have h2 := van W.a₂ node.a₂_mem
  have h6 := (unequalDepthMiddle_constant_unit node d hm).map (algebraMap R K)
  have ha := node.a₁_unit.map (algebraMap R K)
  have he₁ := equation_map W (π ^ k) d.b3 d.b4 d.b6 a'
  have he₂ := equation_map W (π ^ k) d.b3 d.b4 d.b6 c'
  simp only [hs, h2, h3, h4, zero_mul, zero_add, add_zero] at he₁ he₂
  have hprod₁ : v₁ * (v₁ + α * u₁) = algebraMap R K d.b6 := by
    linear_combination he₁
  have hprod₂ : v₂ * (v₂ + α * u₂) = algebraMap R K d.b6 := by
    linear_combination he₂
  have hv₁ : IsUnit v₁ := isUnit_of_mul_isUnit_left (hprod₁.symm ▸ h6)
  have hc₂ : IsUnit (v₂ + α * u₂) := isUnit_of_mul_isUnit_right (hprod₂.symm ▸ h6)
  have hl := dividedTangentRefinement_chord W (π ^ k) d.b3 d.b4 d.b6 a c e
  simp only [hs, h2, h3, h4, zero_mul, add_zero, zero_sub] at hl
  have hu : IsUnit l := isUnit_of_mul_isUnit_left (hl.symm ▸ (ha.mul hv₁).neg)
  have hplus : (l + α) * (v₁ + v₂ + α * u₂) = α * (v₂ + α * u₂) := by
    linear_combination hl
  have hu' : IsUnit (l + α) :=
    isUnit_of_mul_isUnit_left (hplus.symm ▸ ha.mul hc₂)
  have hs' : algebraMap R K π ^ k = 0 := by simpa only [map_pow] using hs
  have hx : e (dividedTangentX W (π ^ k) d.b3 d.b4 d.b6 a c) = l * (l + α) := by
    simp only [dividedTangentX, Affine.addX, map_sub, map_add, map_mul, map_pow,
      map_a₁, map_a₂, AlgHom.commutes, hs', h2, zero_mul, sub_zero]
    ring
  rw [hx]
  exact hu.mul hu'

end FLT.Mazur.WeierstrassDividedDepth

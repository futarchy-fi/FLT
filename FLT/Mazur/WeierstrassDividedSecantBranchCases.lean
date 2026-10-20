/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantResidue
public import FLT.Mazur.WeierstrassDividedTangentThreeDomainCover
public import FLT.Mazur.WeierstrassDividedVerticalSmooth

/-!
# Secants between punctured nodal branches have three possible output domains

Two points on the same branch lie in one of the strict tangent domains.
Two points on opposite branches have a nonzero original output abscissa.
These alternatives are derived from the equations and input derivatives.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve

/-- A smooth point of the split tangent cone has a nonzero abscissa. -/
theorem splitCone_abscissa_ne_zero {K : Type*} [Field K] {t u v : K}
    (he : v * (v + t * u) = 0) (hd : 2 * v + t * u ≠ 0) : u ≠ 0 := by
  intro hu
  have hv : v = 0 := by
    simpa only [hu, mul_zero, add_zero, mul_self_eq_zero] using he
  exact hd (by rw [hu, hv]; ring)

/-- Same-branch secants have a strict tangent denominator; opposite branches have smooth output. -/
theorem splitCone_secant_three_cases {K : Type*} [Field K] {t u₁ u₂ v₁ v₂ l : K}
    (ht : t ≠ 0) (h₁ : v₁ * (v₁ + t * u₁) = 0)
    (h₂ : v₂ * (v₂ + t * u₂) = 0)
    (hd₁ : 2 * v₁ + t * u₁ ≠ 0) (hd₂ : 2 * v₂ + t * u₂ ≠ 0)
    (hl : l * (u₁ - u₂) = v₁ - v₂) :
    (v₁ + v₂ + t * u₁) * v₁ ≠ 0 ∨
      (v₁ + v₂ + t * u₁) * (v₂ + t * u₂) ≠ 0 ∨ l * (l + t) ≠ 0 := by
  have hu₁ := splitCone_abscissa_ne_zero h₁ hd₁
  have hu₂ := splitCone_abscissa_ne_zero h₂ hd₂
  rcases mul_eq_zero.mp h₁ with hv₁ | hv₁ <;> rcases mul_eq_zero.mp h₂ with hv₂ | hv₂
  · right; left
    simpa only [hv₁, hv₂, zero_add] using mul_ne_zero (mul_ne_zero ht hu₁)
      (mul_ne_zero ht hu₂)
  · right; right
    apply opposite_divided_secant_nonzero ht hu₁ hu₂
    linear_combination hl + hv₁ - hv₂
  · right; right
    apply opposite_divided_secant_nonzero ht hu₂ hu₁
    linear_combination -hl - hv₁ + hv₂
  · left
    have he : v₁ + v₂ + t * u₁ = -(t * u₂) := by linear_combination hv₁ + hv₂
    have hy : v₁ = -(t * u₁) := by linear_combination hv₁
    rw [he, hy]
    exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero ht hu₂))
      (neg_ne_zero.mpr (mul_ne_zero ht hu₁))

set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S K : Type u} [CommRing R] [CommRing S] [Field K]
  [Algebra R S] [Algebra R K] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (e : DividedSecantRing W s b3 b4 b6 a c →ₐ[R] K)
local notation "T" => DividedSecantRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "a'" => e.comp ((j).comp a)
local notation "c'" => e.comp ((j).comp c)
local notation "t" => algebraMap R K W.a₁
local notation "E" => dividedTangentDenominator W s b3 b4 b6 c a
local notation "C₂" => dividedTangentBranchFactor W s b3 b4 b6 c

/-- The residue of every secant between derivative-smooth nodal inputs lies in a proved domain. -/
theorem dividedSecant_residue_three_cases
    (hs : algebraMap R K s = 0) (h2 : algebraMap R K W.a₂ = 0)
    (h3 : algebraMap R K b3 = 0) (h4 : algebraMap R K b4 = 0)
    (h6 : algebraMap R K b6 = 0) (ht : t ≠ 0)
    (ha : (a') (verticalDerivative W s b3 b4 b6) ≠ 0)
    (hc : (c') (verticalDerivative W s b3 b4 b6) ≠ 0) :
    e (algebraMap S T (E * a (y W s b3 b4 b6))) ≠ 0 ∨
      e (algebraMap S T (E * C₂)) ≠ 0 ∨
        e (dividedSecantX W s b3 b4 b6 a c) ≠ 0 := by
  have cone (f : Coordinate W s b3 b4 b6 →ₐ[R] K) :
      f (y W s b3 b4 b6) * (f (y W s b3 b4 b6) + t * f (x W s b3 b4 b6)) = 0 := by
    have h := equation_map W s b3 b4 b6 f
    simp only [hs, h2, h3, h4, h6, zero_mul, add_zero] at h
    linear_combination h
  have deriv (f : Coordinate W s b3 b4 b6 →ₐ[R] K) :
      f (verticalDerivative W s b3 b4 b6) =
        2 * f (y W s b3 b4 b6) + t * f (x W s b3 b4 b6) := by
    simp only [verticalDerivative_eq, map_add, map_mul, map_ofNat, AlgHom.commutes,
      h3, add_zero]
  have hl := congrArg e (dividedSecantSlope_relation W s b3 b4 b6 a c)
  simp only [map_mul, map_sub] at hl
  have h := splitCone_secant_three_cases ht (cone a') (cone c')
    (by simpa only [deriv] using ha) (by simpa only [deriv] using hc) hl
  have hx : e (dividedSecantX W s b3 b4 b6 a c) =
      e (dividedSecantSlope W s b3 b4 b6 a c) *
        (e (dividedSecantSlope W s b3 b4 b6 a c) + t) := by
    simp only [dividedSecantX, Affine.addX, map_sub, map_add, map_mul, map_pow,
      map_a₁, map_a₂, AlgHom.commutes, hs, h2, zero_mul, sub_zero]
    ring
  simpa only [hx, dividedTangentDenominator, dividedTangentBranchFactor,
    map_mul, map_add, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
    ← IsScalarTower.algebraMap_apply, AlgHom.commutes, h3, add_zero, zero_add, add_comm] using h

end FLT.Mazur.WeierstrassDilatation

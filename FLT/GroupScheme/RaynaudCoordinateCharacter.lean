/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.AbsoluteGaloisGroup.RootCharacter

/-!
# Raynaud coordinate characters

A coordinate with nth power π^m times a base unit differs from the mth power
of an nth root of π by an integral unit. Inertia fixes the residue of that
unit, so the coordinate character is the mth power of the root character.
This is the algebraic bridge in Raynaud §3.4(9); it does not construct the
coordinates of a finite-flat group scheme.
-/

@[expose] public noncomputable section

open NumberField IsLocalRing

namespace RaynaudParameters

variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ω" => AlgebraicClosure Kv
local notation "A" => IntegralClosure O Ω

/-- A coordinate with power π^m times a unit has an integral unit correction. -/
theorem exists_unit_coordinate_ratio {π : O} {α x : Ω} {n m : ℕ}
    (hn : 0 < n) (hπ : π.1 ≠ 0)
    (hα : α ^ n = algebraMap Kv Ω π.1) (u : Oˣ)
    (hx : x ^ n = (algebraMap Kv Ω π.1) ^ m * algebraMap O Ω (u : O)) :
    ∃ z : Aˣ, algebraMap A Ω (z : A) = x / α ^ m := by
  have hpow : (x / α ^ m) ^ n = algebraMap O Ω (u : O) := by
    rw [div_pow, pow_right_comm, hα, hx, mul_div_cancel_left₀]
    exact pow_ne_zero m ((map_ne_zero (algebraMap Kv Ω)).mpr hπ)
  let z : A := ⟨x / α ^ m, IsIntegral.of_pow hn (by
    rw [hpow]
    exact isIntegral_algebraMap)⟩
  have hz : z ^ n = algebraMap O A (u : O) := by
    apply Subtype.ext
    exact hpow.trans (IsScalarTower.algebraMap_apply O A Ω (u : O))
  have hunit : IsUnit z := (isUnit_pow_iff hn.ne').mp (by
    rw [hz]
    exact IsUnit.map (algebraMap O A) u.isUnit)
  exact ⟨hunit.unit, congrArg Subtype.val hunit.unit_spec⟩

/-- The uniformizer formulation of the integral unit correction. -/
theorem exists_unit_coordinate_ratio_of_uniformizer {π : O} {α x : Ω} {n m : ℕ}
    (hn : 0 < n) (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    (hα : α ^ n = algebraMap Kv Ω π.1) (u : Oˣ)
    (hx : x ^ n = (algebraMap Kv Ω π.1) ^ m * algebraMap O Ω (u : O)) :
    ∃ z : Aˣ, algebraMap A Ω (z : A) = x / α ^ m :=
  exists_unit_coordinate_ratio v hn
    (fun h ↦ IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero
      hπ (Subtype.ext h)) hα u hx

/-- Reduction cancels the integral unit correction in the coordinate ratio. -/
theorem residue_coordinate_ratio {π : O} {α x : Ω} {n m : ℕ}
    (hn : 0 < n) (hπ : π.1 ≠ 0)
    (hα : α ^ n = algebraMap Kv Ω π.1) (u : Oˣ)
    (hx : x ^ n = (algebraMap Kv Ω π.1) ^ m * algebraMap O Ω (u : O))
    (σ : localInertiaGroup v) (r : A) (hr : r.1 = σ.1 x / x) :
    residue A r = (LocalRoot.character v hn hπ hα σ : ResidueField A) ^ m := by
  obtain ⟨z, hz⟩ := exists_unit_coordinate_ratio v hn hπ hα u hx
  change (z : A).1 = x / α ^ m at hz
  have ha0 := LocalRoot.root_ne_zero v hn hπ hα
  have hx0 : x ≠ 0 := by
    intro h
    have hu0 := (IsUnit.map (algebraMap O Ω) u.isUnit).ne_zero
    rw [h, zero_pow hn.ne'] at hx
    exact (mul_ne_zero (pow_ne_zero m ((map_ne_zero (algebraMap Kv Ω)).mpr hπ)) hu0)
      hx.symm
  have hzinv : ((z⁻¹ : Aˣ) : A).1 = (x / α ^ m)⁻¹ := by
    rw [← hz]
    apply eq_inv_of_mul_eq_one_right
    exact congrArg Subtype.val (Units.mul_inv z)
  have he : r = (σ.1 • (z : A)) * ((z⁻¹ : Aˣ) : A) *
      LocalRoot.integralRatio v hn hπ hα σ ^ m := by
    apply Subtype.ext
    change r.1 = σ.1 (z : A).1 * ((z⁻¹ : Aˣ) : A).1 * (σ.1 α / α) ^ m
    rw [hr, hz, hzinv, map_div₀, map_pow, div_pow]
    field_simp [ha0, hx0]
  rw [he, map_mul, map_mul, residue_smul_eq, ← map_mul, Units.mul_inv, map_one,
    one_mul, map_pow]
  rfl

/-- A coordinate root character is the corresponding power of the uniformizer-root character. -/
theorem coordinate_character {π : O} {α x : Ω} {n m : ℕ} {a : Kv}
    (hn : 0 < n) (hπ : π.1 ≠ 0)
    (hα : α ^ n = algebraMap Kv Ω π.1) (u : Oˣ)
    (ha : a ≠ 0) (hxa : x ^ n = algebraMap Kv Ω a)
    (hx : x ^ n = (algebraMap Kv Ω π.1) ^ m * algebraMap O Ω (u : O))
    (σ : localInertiaGroup v) :
    LocalRoot.character v hn ha hxa σ = LocalRoot.character v hn hπ hα σ ^ m := by
  apply Units.ext
  exact residue_coordinate_ratio v hn hπ hα u hx σ
    (LocalRoot.integralRatio v hn ha hxa σ) rfl

end RaynaudParameters

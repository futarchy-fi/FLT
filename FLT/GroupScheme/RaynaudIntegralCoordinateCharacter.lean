/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.RootCharacter
public import FLT.GroupScheme.RaynaudIntegralUnitCorrection

/-!
# Inertia ratios for coordinates with integral extension coefficients

The correction unit lies in the original integral closure. Original inertia
therefore fixes its residue even when the coefficients came from a larger
integral ring. Compatible placement of the actual model in this closure is
still required when applying the theorem to a descended Raynaud model.
-/

@[expose] public noncomputable section
namespace RaynaudParameters
open NumberField IsLocalRing

variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ω" => AlgebraicClosure Kv
local notation "A" => IntegralClosure O Ω

/-- Integral coefficient extensions give the same reduced root-character power over the base. -/
theorem exists_integral_coordinate_ratio
    {R : Type*} [CommRing R] (f : R →+* Ω) (hf : ∀ r, IsIntegral O (f r))
    {π : Kv} {α x : Ω} {n m : ℕ} (hn : 0 < n) (hπ : π ≠ 0)
    (hα : α ^ n = algebraMap Kv Ω π) (u : Rˣ)
    (hx : x ^ n = (algebraMap Kv Ω π) ^ m * f u) (σ : localInertiaGroup v) :
    ∃ r : A, r.val = σ.1 x / x ∧
      residue A r = (LocalRoot.character v hn hπ hα σ : ResidueField A) ^ m := by
  obtain ⟨z, hz⟩ := exists_integral_unit_coordinate_ratio f hf hn
    ((map_ne_zero (algebraMap Kv Ω)).mpr hπ) hα u hx
  have ha0 := LocalRoot.root_ne_zero v hn hπ hα
  have hx0 : x ≠ 0 := by
    intro h
    have hu0 := (u.isUnit.map f).ne_zero
    rw [h, zero_pow hn.ne'] at hx
    exact (mul_ne_zero (pow_ne_zero m ((map_ne_zero (algebraMap Kv Ω)).mpr hπ)) hu0)
      hx.symm
  have hzinv : ((z⁻¹ : Aˣ) : A).val = (x / α ^ m)⁻¹ := by
    rw [← hz]
    apply eq_inv_of_mul_eq_one_right
    exact congrArg Subtype.val (Units.mul_inv z)
  let r : A := (σ.1 • (z : A)) * ((z⁻¹ : Aˣ) : A) *
    LocalRoot.integralRatio v hn hπ hα σ ^ m
  refine ⟨r, ?_, ?_⟩
  · change σ.1 (z : A).val * ((z⁻¹ : Aˣ) : A).val * (σ.1 α / α) ^ m = σ.1 x / x
    rw [hz, hzinv, map_div₀, map_pow, div_pow]
    field_simp [ha0, hx0]
  · change residue A ((σ.1 • (z : A)) * ((z⁻¹ : Aˣ) : A) *
      LocalRoot.integralRatio v hn hπ hα σ ^ m) = _
    rw [map_mul, map_mul, residue_smul_eq, ← map_mul, Units.mul_inv,
      map_one, one_mul, map_pow]
    rfl

end RaynaudParameters

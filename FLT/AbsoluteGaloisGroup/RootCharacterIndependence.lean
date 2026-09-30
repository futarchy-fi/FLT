/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.AbsoluteGaloisGroup.RootCharacter

/-!
# Independence of the root in a reduced inertia character

Changing a root by an integral unit leaves its reduced character unchanged.
In particular the character of a root of a fixed nonzero element does not
depend on the chosen root, in every positive degree.
-/

@[expose] public section

open NumberField

namespace LocalRoot

variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation3 "L" => AlgebraicClosure (v.adicCompletion K)
local notation3 "A" => IntegralClosure (v.adicCompletionIntegers K) L

variable {n : ℕ} (hn : 0 < n) {a b : v.adicCompletion K} (ha : a ≠ 0) (hb : b ≠ 0)

variable {α β : AlgebraicClosure (v.adicCompletion K)}
  (hα : α ^ n = algebraMap (v.adicCompletion K)
    (AlgebraicClosure (v.adicCompletion K)) a)
  (hβ : β ^ n = algebraMap (v.adicCompletion K)
    (AlgebraicClosure (v.adicCompletion K)) b)

/-- Roots whose ratio is an integral unit give the same reduced character. -/
theorem character_eq_of_unit_ratio (z : Aˣ) (hz : (z : A).1 = β / α) :
    character v hn hb hβ = character v hn ha hα := by
  apply MonoidHom.ext
  intro σ
  apply Units.ext
  have hzinv : ((z⁻¹ : Aˣ) : A).1 = (β / α)⁻¹ := by
    calc
      ((z⁻¹ : Aˣ) : A).1 = ((z : A).1)⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        exact congrArg (fun x : A ↦ x.1) (Units.mul_inv z)
      _ = (β / α)⁻¹ := congrArg Inv.inv hz
  have hratio : integralRatio v hn hb hβ σ =
      (σ.1 • (z : A)) * ((z⁻¹ : Aˣ) : A) * integralRatio v hn ha hα σ := by
    apply Subtype.ext
    change σ.1 β / β = σ.1 (z : A).1 * ((z⁻¹ : Aˣ) : A).1 * (σ.1 α / α)
    rw [hz, hzinv]
    simp only [map_div₀]
    field_simp [root_ne_zero v hn ha hα, root_ne_zero v hn hb hβ]
  change IsLocalRing.residue A (integralRatio v hn hb hβ σ) =
    IsLocalRing.residue A (integralRatio v hn ha hα σ)
  rw [hratio, map_mul, map_mul, residue_smul_eq, ← map_mul, Units.mul_inv,
    map_one, one_mul]

include hn ha hα in
/-- The ratio of two roots of the same nonzero element is an integral unit. -/
theorem exists_unit_ratio_of_same_power
    {β : AlgebraicClosure (v.adicCompletion K)}
    (hβ : β ^ n = algebraMap (v.adicCompletion K) L a) :
    ∃ z : Aˣ, (z : A).1 = β / α := by
  have hpow : (β / α) ^ n = 1 := by
    rw [div_pow, hβ, hα]
    exact div_self ((map_ne_zero (algebraMap (v.adicCompletion K) L)).mpr ha)
  let z : A := ⟨β / α, IsIntegral.of_pow hn (hpow ▸ isIntegral_one)⟩
  have hzpow : z ^ n = 1 := Subtype.ext hpow
  have hzunit : IsUnit z := (isUnit_pow_iff hn.ne').mp (hzpow ▸ isUnit_one)
  exact ⟨hzunit.unit, congrArg Subtype.val hzunit.unit_spec⟩

include hn ha hα in
/-- The reduced root character is independent of the chosen root. -/
theorem character_root_independent
    {β : AlgebraicClosure (v.adicCompletion K)}
    (hβ : β ^ n = algebraMap (v.adicCompletion K) L a) :
    character v hn ha hβ = character v hn ha hα := by
  obtain ⟨z, hz⟩ := exists_unit_ratio_of_same_power v hn ha hα hβ
  exact character_eq_of_unit_ratio v hn ha ha hα hβ z hz

end LocalRoot

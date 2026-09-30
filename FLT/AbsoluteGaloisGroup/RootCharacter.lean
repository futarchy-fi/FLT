/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.AbsoluteGaloisGroup.TameCharacter

/-!
# Reduced root characters of arbitrary degree

The reduction of `σ(α) / α`, for a root of a nonzero base-field element,
is a character of inertia. Taking powers of the root takes powers of the
character. This supplies the raw construction for higher fundamental
characters; it does not assert independence of roots or identify a finite
coefficient field.
-/

@[expose] public section

open NumberField

namespace LocalRoot

variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation3 "L" => AlgebraicClosure (v.adicCompletion K)
local notation3 "A" => IntegralClosure (v.adicCompletionIntegers K) L

variable {n : ℕ} (hn : 0 < n) {a : v.adicCompletion K} (ha : a ≠ 0)
variable {α : AlgebraicClosure (v.adicCompletion K)}
  (hα : α ^ n = algebraMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) a)

include hn ha hα in
/-- A root of a nonzero element is nonzero. -/
theorem root_ne_zero : α ≠ 0 := by
  intro h
  rw [h, zero_pow hn.ne'] at hα
  exact (map_ne_zero (algebraMap (v.adicCompletion K) L)).mpr ha hα.symm

include ha hα in
/-- The inertia ratio has order dividing the root degree. -/
theorem ratio_pow (σ : localInertiaGroup v) : (σ.1 α / α) ^ n = 1 := by
  rw [div_pow, ← map_pow, hα, AlgEquiv.commutes, div_self]
  exact (map_ne_zero (algebraMap (v.adicCompletion K) L)).mpr ha

/-- The ratio is integral because it is a root of unity. -/
noncomputable def integralRatio (σ : localInertiaGroup v) : A :=
  ⟨σ.1 α / α, IsIntegral.of_pow hn <| by
    rw [ratio_pow v ha hα σ]
    exact isIntegral_one⟩

/-- The same order relation holds before reducing the integral ratio. -/
theorem integralRatio_pow (σ : localInertiaGroup v) :
    integralRatio v hn ha hα σ ^ n = 1 := by
  apply Subtype.ext
  exact ratio_pow v ha hα σ

/-- The integral ratios satisfy the multiplicative cocycle identity. -/
theorem integralRatio_mul (σ τ : localInertiaGroup v) :
    integralRatio v hn ha hα (σ * τ) =
      (σ.1 • integralRatio v hn ha hα τ) * integralRatio v hn ha hα σ := by
  apply Subtype.ext
  change (σ.1 * τ.1) α / α = σ.1 (τ.1 α / α) * (σ.1 α / α)
  rw [AlgEquiv.mul_apply, map_div₀]
  field_simp [root_ne_zero v hn ha hα]

/-- The reduced root ratio, bundled as a unit of the residue field. -/
noncomputable def ratioUnit (σ : localInertiaGroup v) :
    (IsLocalRing.ResidueField A)ˣ := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact (rootsOfUnity.mkOfPowEq (n := n) (IsLocalRing.residue A (integralRatio v hn ha hα σ))
    (by rw [← map_pow, integralRatio_pow, map_one])).1

/-- The underlying residue-field element of the ratio unit. -/
@[simp] theorem coe_ratioUnit (σ : localInertiaGroup v) :
    (ratioUnit v hn ha hα σ : IsLocalRing.ResidueField A) =
      IsLocalRing.residue A (integralRatio v hn ha hα σ) := rfl

/-- Reduction turns the cocycle into a character because inertia fixes residues. -/
noncomputable def character : localInertiaGroup v →* (IsLocalRing.ResidueField A)ˣ where
  toFun := ratioUnit v hn ha hα
  map_one' := by
    apply Units.ext
    rw [coe_ratioUnit]
    have h : integralRatio v hn ha hα 1 = 1 := by
      apply Subtype.ext
      exact div_self (root_ne_zero v hn ha hα)
    simp [h]
  map_mul' σ τ := by
    apply Units.ext
    simp only [coe_ratioUnit, Units.val_mul, integralRatio_mul, map_mul, residue_smul_eq]
    exact mul_comm _ _

/-- The character has exponent dividing the root degree. -/
theorem character_pow (σ : localInertiaGroup v) : character v hn ha hα σ ^ n = 1 := by
  apply Units.ext
  change (IsLocalRing.residue A (integralRatio v hn ha hα σ)) ^ n = 1
  rw [← map_pow, integralRatio_pow, map_one]

/-- Taking an integral power of a root takes the same power of its character. -/
theorem character_root_pow (m : ℕ) (σ : localInertiaGroup v) :
    character v hn ha hα σ ^ m =
      character v hn (pow_ne_zero m ha)
        (show (α ^ m) ^ n = algebraMap (v.adicCompletion K) L (a ^ m) by
          rw [pow_right_comm, hα, map_pow]) σ := by
  apply Units.ext
  change (IsLocalRing.residue A (integralRatio v hn ha hα σ)) ^ m = _
  rw [← map_pow]
  congr 1
  apply Subtype.ext
  change (σ.1 α / α) ^ m = σ.1 (α ^ m) / α ^ m
  rw [div_pow, map_pow]

/-- Compatible roots of degrees `n * m` and `n` give compatible characters. -/
theorem character_degree_mul (m : ℕ) (hm : 0 < m)
    {β : AlgebraicClosure (v.adicCompletion K)}
    (hβ : β ^ (n * m) = algebraMap (v.adicCompletion K) L a)
    (σ : localInertiaGroup v) :
    character v (Nat.mul_pos hn hm) ha hβ σ ^ m =
      character v hn ha
        (show (β ^ m) ^ n = algebraMap (v.adicCompletion K) L a by
          rw [← pow_mul, Nat.mul_comm m n, hβ]) σ := by
  apply Units.ext
  change (IsLocalRing.residue A (integralRatio v (Nat.mul_pos hn hm) ha hβ σ)) ^ m = _
  rw [← map_pow]
  congr 1
  apply Subtype.ext
  change (σ.1 β / β) ^ m = σ.1 (β ^ m) / β ^ m
  rw [div_pow, map_pow]

end LocalRoot

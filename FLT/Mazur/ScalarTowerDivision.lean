/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Exact.Basic

/-!
# Scalar division in a compatible module tower

Surjective transitions with the truncated scalar kernel and annihilator
identities permit compatible division by the parameter. Division is chosen
one stage higher and then restricted; the annihilator identity makes these
choices compatible. No completeness or flatness assumption on the limit is used.
-/

@[expose] public noncomputable section

universe u v

namespace FLT.Mazur.ScalarTowerDivision

variable {R : Type u} [CommRing R] {M : ℕ → Type v}
  [∀ m, AddCommGroup (M m)] [∀ m, Module R (M m)]
  (r : R) (f : ∀ m, M (m + 1) →ₗ[R] M m)

/-- Compatibility with each specified adjacent transition. -/
def Compatible (s : ∀ m, M m) : Prop := ∀ m, f m (s (m + 1)) = s m

/-- The annihilator identities alone rule out parameter torsion in the limit. -/
theorem compatible_smul_injective
    (ha : ∀ m (x : M (m + 1)), r • x = 0 ↔ f m x = 0)
    (s : ∀ m, M m) (hs : Compatible f s) (hz : ∀ m, r • s m = 0) :
    ∀ m, s m = 0 := by
  intro m
  rw [← hs m]
  exact (ha m _).mp (hz (m + 1))

/-- Every section vanishing on stage zero is divisible at every finite stage. -/
theorem stage_divisible
    (hf : ∀ m, Function.Surjective (f m))
    (hk : ∀ m (x : M (m + 1)), f m x = 0 ↔ ∃ y, r ^ (m + 1) • y = x)
    (s : ∀ m, M m) (hs : Compatible f s) (h₀ : s 0 = 0) :
    ∀ m, ∃ y : M m, r • y = s m := by
  intro m
  induction m with
  | zero => exact ⟨0, (smul_zero r).trans h₀.symm⟩
  | succ m ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨z, hz⟩ := hf m y
    have he : f m (s (m + 1) - r • z) = 0 := by
      rw [map_sub, map_smul, hs m, hz, hy, sub_self]
    obtain ⟨w, hw⟩ := (hk m _).mp he
    refine ⟨z + r ^ m • w, ?_⟩
    rw [smul_add, smul_smul, ← pow_succ', hw]
    rw [add_comm (r • z), sub_add_cancel]

/-- Dividing one stage higher produces an actual compatible division. -/
theorem exists_compatible_division
    (hf : ∀ m, Function.Surjective (f m))
    (hk : ∀ m (x : M (m + 1)), f m x = 0 ↔ ∃ y, r ^ (m + 1) • y = x)
    (ha : ∀ m (x : M (m + 1)), r • x = 0 ↔ f m x = 0)
    (s : ∀ m, M m) (hs : Compatible f s) (h₀ : s 0 = 0) :
    ∃ t : ∀ m, M m, Compatible f t ∧ ∀ m, r • t m = s m := by
  choose v hv using stage_divisible r f hf hk s hs h₀
  let t (m : ℕ) := f m (v (m + 1))
  have ht (m : ℕ) : r • t m = s m := by
    change r • f m (v (m + 1)) = s m
    rw [← map_smul, hv, hs]
  refine ⟨t, ?_, ht⟩
  intro m
  have hz : r • (f (m + 1) (v (m + 2)) - v (m + 1)) = 0 := by
    rw [smul_sub, ← map_smul, hv, hs, hv, sub_self]
  have he := (ha m _).mp hz
  rw [map_sub, sub_eq_zero] at he
  exact he

/-- Repeated compatible division identifies every finite-stage kernel with a scalar power. -/
theorem exists_compatible_power_division
    (hf : ∀ m, Function.Surjective (f m))
    (hk : ∀ m (x : M (m + 1)), f m x = 0 ↔ ∃ y, r ^ (m + 1) • y = x)
    (ha : ∀ m (x : M (m + 1)), r • x = 0 ↔ f m x = 0)
    (m : ℕ) (s : ∀ a, M a) (hs : Compatible f s) (hz : s m = 0) :
    ∃ t : ∀ a, M a, Compatible f t ∧ ∀ a, r ^ (m + 1) • t a = s a := by
  induction m generalizing s with
  | zero =>
    simpa only [Nat.zero_add, pow_one] using exists_compatible_division r f hf hk ha s hs hz
  | succ m ih =>
    have hzero : ∀ a, s a = 0 → s 0 = 0 := by
      intro a
      induction a with
      | zero => exact id
      | succ a ih =>
        intro h
        apply ih
        rw [← hs a, h, map_zero]
    obtain ⟨u, hu, he⟩ := exists_compatible_division r f hf hk ha s hs (hzero _ hz)
    have hum : u m = 0 := by
      rw [← hu m]
      exact (ha m _).mp ((he (m + 1)).trans hz)
    obtain ⟨t, ht, htu⟩ := ih u hu hum
    refine ⟨t, ht, fun a ↦ ?_⟩
    rw [pow_succ', mul_smul, htu, he]

end FLT.Mazur.ScalarTowerDivision

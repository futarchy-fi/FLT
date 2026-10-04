/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Tactic.Abel

/-! # Lifting generators through a nilpotent scalar -/

@[expose] public section
namespace LinearMap
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]

/-- Surjectivity modulo a nilpotent scalar implies actual surjectivity. -/
theorem surjective_of_scalar_nilpotent (f : M →ₗ[R] N) (r : R) (n : ℕ)
    (hn : ∀ x : N, r ^ n • x = 0)
    (h : ∀ x : N, ∃ a b, f a + r • b = x) : Function.Surjective f := by
  have lift (k : ℕ) (x : N) : ∃ a b, f a + r ^ k • b = x := by
    induction k with
    | zero => exact ⟨0, x, by simp⟩
    | succ k ih =>
      obtain ⟨a, b, hab⟩ := ih
      obtain ⟨c, d, hcd⟩ := h b
      refine ⟨a + r ^ k • c, d, ?_⟩
      rw [map_add, map_smul, pow_succ, mul_smul, add_assoc, ← smul_add, hcd, hab]
  intro x
  obtain ⟨a, b, hab⟩ := lift n x
  exact ⟨a, by simpa only [hn, add_zero] using hab⟩

end LinearMap

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# A finite-power criterion for lifting after principal restriction

In a commuting square with source localization, a restricted target element
comes from the localized source exactly when a power multiple comes from the
original source. Only power torsion in the target restriction kernel is needed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PrincipalImageCriterion
variable {A B A' B' : Type*}
  [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  (f : A →+* B) (a : A →+* A') (b : B →+* B') (f' : A' →+* B')
  (h : ∀ x, f' (a x) = b (f x)) (s : A)
  (hloc : @IsLocalization.Away _ _ s A' _ a.toAlgebra)
  (hzero : ∀ x, b x = 0 → ∃ n : ℕ, f s ^ n * x = 0)
include h hloc hzero

/-- A local lift is equivalent to an original lift after one finite power. -/
theorem lift_iff (y : B) :
    (∃ x : A', f' x = b y) ↔ ∃ (n : ℕ) (x : A), f x = f s ^ n * y := by
  let _ := a.toAlgebra
  let _ : IsLocalization.Away s A' := hloc
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨n, x, hx⟩ := IsLocalization.Away.surj s z
    change z * a s ^ n = a x at hx
    have he : b (f s ^ n * y - f x) = 0 := by
      rw [map_sub, map_mul, map_pow, ← h, ← h, ← hz, ← map_pow, ← map_mul]
      rw [mul_comm, hx, sub_self]
    obtain ⟨m, hm⟩ := hzero _ he
    refine ⟨m + n, s ^ m * x, ?_⟩
    rw [map_mul, map_pow, pow_add, mul_assoc]
    exact (sub_eq_zero.mp (by simpa only [mul_sub] using hm)).symm
  · rintro ⟨n, x, hx⟩
    obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit s (S := A')
    change (u : A') = a s at hu
    refine ⟨(↑(u⁻¹) : A') ^ n * a x, ?_⟩
    rw [map_mul, h, hx]
    simp only [map_pow, map_mul]
    rw [← h s, ← hu, ← mul_assoc, ← mul_pow, ← map_mul]
    simp

end FLT.Mazur.PrincipalImageCriterion

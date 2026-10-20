/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Clearing denominators of local trace units

A compatible local trace-one element forces a power of the localization
parameter into the original trace range, including over nonreduced rings.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.LocalizedTracePower
variable {R B C D : Type*} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
  [Algebra R B] [Algebra R C] [Algebra B D]
  (r : R) [IsLocalization.Away r C]
  [IsLocalization.Away (algebraMap R B r) D]
  (β : C →+* D) (τ : B →ₗ[R] R) (T : D → C)
  (hsquare : ∀ a, algebraMap B D (algebraMap R B a) = β (algebraMap R C a))
  (hT : ∀ b, T (algebraMap B D b) = algebraMap R C (τ b))
  (hlinear : ∀ a b, T (β a * b) = a * T b)

include hsquare hT hlinear in
/-- A local trace-one element gives a power in the unchanged global trace range. -/
theorem exists_power_mem_range (hone : ∃ z, T z = 1) :
    ∃ n : ℕ, r ^ n ∈ LinearMap.range τ := by
  obtain ⟨z, hz⟩ := hone
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj (algebraMap R B r) z
  have he : algebraMap R C (τ b) = algebraMap R C (r ^ n) := by
    rw [← hT, ← hb, mul_comm, hsquare, ← map_pow, hlinear, hz, mul_one, map_pow]
  obtain ⟨s, hs⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers r) C).mp he
  obtain ⟨m, hm⟩ := s.property
  have hpow : r ^ m * τ b = r ^ (m + n) := by
    simpa only [← hm, pow_add] using hs
  refine ⟨m + n, ⟨r ^ m • b, ?_⟩⟩
  simpa only [map_smul, smul_eq_mul] using hpow

end FLT.Mazur.LocalizedTracePower

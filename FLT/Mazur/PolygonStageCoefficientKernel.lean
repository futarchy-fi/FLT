/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalStageReduction

/-!
# Kernels of the actual truncated coefficient maps

The adjacent coefficient kernel is the last parameter power. Multiplication
by that power has kernel the parameter ideal, over an arbitrary base ring.
These identities supply the coefficient sequence to transport by flatness.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.PolygonInfinitesimalStages

variable (R : Type*) [CommRing R] (m : ℕ)

/-- Adjacent restriction preserves the polynomial representative. -/
@[simp] theorem restriction_mk (p : R[X]) :
    restriction R m (AdjoinRoot.mk _ p) = AdjoinRoot.mk _ p := by
  change p.eval₂ (algebraMap R _) (parameter R m) = _
  exact AdjoinRoot.aeval_eq p

/-- Every coefficient at one stage lifts to the next stage. -/
theorem restriction_surjective : Function.Surjective (restriction R m) := by
  intro z
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  exact ⟨AdjoinRoot.mk _ p, restriction_mk R m p⟩

/-- The adjacent coefficient kernel is exactly the last parameter power. -/
theorem restriction_eq_zero_iff (z : Ring R (m + 1)) :
    restriction R m z = 0 ↔ ∃ w, parameter R (m + 1) ^ (m + 1) * w = z := by
  constructor
  · obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    rw [restriction_mk, AdjoinRoot.mk_eq_zero]
    rintro ⟨q, rfl⟩
    exact ⟨AdjoinRoot.mk _ q, by rw [map_mul, map_pow]; rfl⟩
  · rintro ⟨w, rfl⟩
    rw [map_mul, map_pow, restriction_parameter, parameter_pow, zero_mul]

/-- The closed coefficient fiber has the principal parameter ideal as kernel. -/
theorem reduction_eq_zero_iff (z : Ring R m) :
    reduction R m z = 0 ↔ ∃ w, parameter R m * w = z := by
  constructor
  · obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    rw [reduction_mk, ← Polynomial.X_dvd_iff]
    rintro ⟨q, rfl⟩
    exact ⟨AdjoinRoot.mk _ q, by rw [map_mul]; rfl⟩
  · rintro ⟨w, rfl⟩
    rw [map_mul, reduction_parameter, zero_mul]

/-- The annihilator of the last parameter power is exactly the parameter ideal. -/
theorem parameter_last_mul_eq_zero_iff (z : Ring R (m + 1)) :
    parameter R (m + 1) ^ (m + 1) * z = 0 ↔ reduction R (m + 1) z = 0 := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  change AdjoinRoot.mk _ ((X : R[X]) ^ (m + 1)) * AdjoinRoot.mk _ p = 0 ↔ _
  rw [← map_mul, AdjoinRoot.mk_eq_zero, reduction_mk, Polynomial.X_pow_dvd_iff]
  constructor
  · intro hp
    simpa only [coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self] using
      hp (m + 1) (Nat.lt_succ_self _)
  · intro hp d hd
    rw [coeff_X_pow_mul']
    split_ifs with h
    · have he : d = m + 1 := by omega
      simp only [he, Nat.sub_self, hp]
    · rfl

/-- The annihilator of the parameter is the adjacent coefficient kernel. -/
theorem parameter_mul_eq_zero_iff (z : Ring R (m + 1)) :
    parameter R (m + 1) * z = 0 ↔ restriction R m z = 0 := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  change AdjoinRoot.mk _ (X : R[X]) * AdjoinRoot.mk _ p = 0 ↔ _
  rw [← map_mul, AdjoinRoot.mk_eq_zero, restriction_mk, AdjoinRoot.mk_eq_zero,
    Polynomial.X_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  constructor
  · intro hp d hd
    simpa only [coeff_X_mul] using hp (d + 1) (by omega)
  · intro hp d hd
    cases d with
    | zero => exact coeff_X_mul_zero p
    | succ d => simpa only [coeff_X_mul] using hp d (by omega)

end FLT.Mazur.PolygonInfinitesimalStages

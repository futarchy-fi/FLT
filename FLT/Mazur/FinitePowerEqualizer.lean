/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Clearing finitely many power-torsion equalizer discrepancies

A compatible scalar whose powers kill each discrepancy gives one uniform power
and an actual compatible multiple. The exponent is constructed from the finite
set of equations; no reducedness or cancellation of the scalar is required.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FinitePowerEqualizer
variable {A : Type*} [CommRing A] {ι : Type*} [Finite ι]
  {B : ι → Type*} [∀ j, CommRing (B j)] (p q : ∀ j, A →+* B j)

/-- One exponent kills a finite family whenever an individual exponent kills each member. -/
theorem exists_uniform_power (r : ∀ j, B j) (v : ∀ j, B j)
    (h : ∀ j, ∃ n : ℕ, r j ^ n * v j = 0) :
    ∃ n : ℕ, ∀ j, r j ^ n * v j = 0 := by
  classical
  let _ := Fintype.ofFinite ι
  choose e he using h
  refine ⟨Finset.univ.sup e, fun j ↦ ?_⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le
    (Finset.le_sup (f := e) (Finset.mem_univ j))
  rw [hm, pow_add, mul_assoc, mul_left_comm, he j, mul_zero]

/-- Multiplying by a constructed power solves all the original equations simultaneously. -/
theorem exists_compatible_power_mul (r v : A) (hr : ∀ j, p j r = q j r)
    (hv : ∀ j, ∃ n : ℕ, p j r ^ n * (p j v - q j v) = 0) :
    ∃ n : ℕ, ∀ j, p j (r ^ n * v) = q j (r ^ n * v) := by
  obtain ⟨n, hn⟩ := exists_uniform_power (fun j ↦ p j r)
    (fun j ↦ p j v - q j v) hv
  refine ⟨n, fun j ↦ ?_⟩
  simpa only [map_mul, map_pow, ← hr j, mul_sub, sub_eq_zero] using hn j

omit [Finite ι] in
/-- A compatible scalar preserves every equation already solved by a section. -/
theorem compatible_mul (r v : A) (hr : ∀ j, p j r = q j r)
    (hv : ∀ j, p j v = q j v) : ∀ j, p j (r * v) = q j (r * v) := by
  intro j
  simp only [map_mul, hr j, hv j]

end FLT.Mazur.FinitePowerEqualizer

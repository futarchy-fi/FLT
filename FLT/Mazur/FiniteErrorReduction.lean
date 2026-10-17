/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Nakayama

/-!
# Exact lifts from a finite one-step error reduction

A finite error module whose generators can be corrected modulo its ideal
multiple has a single multiplier making every error exactly correctable.
The scalar ring and the ambient modules need not be Noetherian or finite.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteErrorReduction
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (F : M →ₗ[R] N) (I : Ideal R) (E : Submodule R N)

/-- One-step reduction makes the finite cokernel image equal to its ideal multiple. -/
theorem cokernel_le_smul
    (h : ∀ y ∈ E, ∃ z : M, y - F z ∈ I • E) :
    E.map (LinearMap.range F).mkQ ≤ I • E.map (LinearMap.range F).mkQ := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz⟩ := h y hy
  have he := Submodule.mem_map_of_mem (f := (LinearMap.range F).mkQ) hz
  rw [Submodule.map_smul''] at he
  have hf : (LinearMap.range F).mkQ (F z) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, rfl⟩
  simpa only [map_sub, hf, sub_zero] using he

/-- A single scalar near one makes every element of the finite error module lift exactly. -/
theorem exists_common_multiplier (hE : E.FG)
    (h : ∀ y ∈ E, ∃ z : M, y - F z ∈ I • E) :
    ∃ a : R, a - 1 ∈ I ∧ ∀ y ∈ E, ∃ z : M, F z = a • y := by
  obtain ⟨a, ha, hz⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
      (E.map (LinearMap.range F).mkQ) (hE.map _) (cokernel_le_smul F I E h)
  refine ⟨a, ha, fun y hy ↦ ?_⟩
  apply (LinearMap.mem_range).mp
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change (LinearMap.range F).mkQ (a • y) = 0
  rw [map_smul]
  exact hz _ (Submodule.mem_map_of_mem hy)

/-- An initial approximate lift and finite one-step reductions construct an exact scaled lift. -/
theorem exists_scaled_lift (hE : E.FG)
    (h : ∀ y ∈ E, ∃ z : M, y - F z ∈ I • E)
    (y : N) (z₀ : M) (hy : y - F z₀ ∈ E) :
    ∃ (a : R) (z : M), a - 1 ∈ I ∧ F z = a • y := by
  obtain ⟨a, ha, hz⟩ := exists_common_multiplier F I E hE h
  obtain ⟨w, hw⟩ := hz _ hy
  refine ⟨a, w + a • z₀, ha, ?_⟩
  rw [map_add, map_smul, hw, smul_sub, sub_add_cancel]

end FLT.Mazur.FiniteErrorReduction

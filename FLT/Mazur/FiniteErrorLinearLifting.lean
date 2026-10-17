/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Filtration

/-!
# Exact linear lifts from approximations with uniformly finite errors

The ambient modules need not be finite. Only the errors, after passage to the
cokernel, must lie at every ideal power in one fixed finitely generated module.
Krull intersection produces a multiplier congruent to one and an exact lift.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteErrorLinearLifting
variable {R M N : Type*} [CommRing R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A finite error module gives a single annihilator congruent to one. -/
theorem exists_annihilator (I : Ideal R) (E : Submodule R N) (hE : E.FG)
    (y : N) (hy : ∀ n : ℕ, y ∈ I ^ n • E) :
    ∃ a : R, a - 1 ∈ I ∧ a • y = 0 := by
  let _ : Module.Finite R E := Module.Finite.of_fg hE
  have hyE : y ∈ E := by simpa using hy 0
  let v : E := ⟨y, hyE⟩
  have hv : v ∈ (⨅ n : ℕ, I ^ n • ⊤ : Submodule R E) := by
    rw [Submodule.mem_iInf]
    intro n
    exact (Submodule.mem_smul_top_iff _ E v).mpr (hy n)
  obtain ⟨r, hr⟩ := (I.mem_iInf_smul_pow_eq_bot_iff v).mp hv
  refine ⟨1 - r.val, ?_, ?_⟩
  · simpa only [sub_sub_cancel_left] using I.neg_mem r.property
  · have he : r.val • y = y := congrArg Subtype.val hr
    rw [sub_smul, one_smul, he, sub_self]

/-- Finite cokernel errors construct an actual preimage after one multiplier. -/
theorem exists_scaled_lift (F : M →ₗ[R] N) (I : Ideal R)
    (E : Submodule R (N ⧸ LinearMap.range F)) (hE : E.FG)
    (y : N) (hy : ∀ n : ℕ, (LinearMap.range F).mkQ y ∈ I ^ n • E) :
    ∃ (a : R) (z : M), a - 1 ∈ I ∧ F z = a • y := by
  obtain ⟨a, ha, he⟩ := exists_annihilator I E hE _ hy
  have hz : a • y ∈ LinearMap.range F := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (LinearMap.range F).mkQ (a • y) = 0
    rw [map_smul, he]
  obtain ⟨z, hz⟩ := hz
  exact ⟨a, z, ha, hz⟩

/-- Actual approximations with errors in one finite ambient module give finite cokernel errors. -/
theorem exists_scaled_lift_of_errors (F : M →ₗ[R] N) (I : Ideal R)
    (E : Submodule R N) (hE : E.FG) (y : N)
    (hy : ∀ n : ℕ, ∃ z : M, y - F z ∈ I ^ n • E) :
    ∃ (a : R) (z : M), a - 1 ∈ I ∧ F z = a • y := by
  apply exists_scaled_lift F I (E.map (LinearMap.range F).mkQ) (hE.map _) y
  intro n
  obtain ⟨z, hz⟩ := hy n
  have he := Submodule.mem_map_of_mem (f := (LinearMap.range F).mkQ) hz
  rw [Submodule.map_smul''] at he
  have hf : (LinearMap.range F).mkQ (F z) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, rfl⟩
  simpa only [map_sub, hf, sub_zero] using he

omit [IsNoetherianRing R] in
/-- The constructed multiplier avoids every proper ideal containing the approximation ideal. -/
theorem multiplier_not_mem (I P : Ideal R) (hIP : I ≤ P) (hP : P ≠ ⊤)
    {a : R} (ha : a - 1 ∈ I) : a ∉ P := by
  intro h
  apply hP
  apply (Ideal.eq_top_iff_one _).mpr
  have := P.sub_mem h (hIP ha)
  simpa only [sub_sub_cancel] using this

end FLT.Mazur.FiniteErrorLinearLifting

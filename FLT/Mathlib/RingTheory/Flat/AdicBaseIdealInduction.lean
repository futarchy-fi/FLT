/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.AdicInjectivityInduction

/-! # Adic injectivity with an additional base ideal -/

@[expose] public noncomputable section

namespace Module.Flat

variable {R N M : Type*} [CommRing R]
  [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]

/-- A quotient transition whose kernel is annihilated by a maximal ideal
transfers tensor injectivity from its residue and right-hand quotient. -/
theorem lTensor_quotient_injective_step [Flat R M] (I J K : Ideal R) [I.IsMaximal]
    (hKJ : K ≤ J) (hIJ : I * J ≤ K) (f : N →ₗ[R] M)
    (hI : Function.Injective (f.lTensor (R ⧸ I)))
    (hJ : Function.Injective (f.lTensor (R ⧸ J))) :
    Function.Injective (f.lTensor (R ⧸ K)) := by
  let p : (R ⧸ K) →ₗ[R] R ⧸ J := Submodule.factor hKJ
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk K x, rfl⟩
  have ht : Module.IsTorsionBySet R p.ker I := by
    intro x r
    apply Subtype.ext
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x : R ⧸ K)
    have haJ : a ∈ J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change p (Ideal.Quotient.mk K a) = 0
      rw [ha]
      exact x.property
    change r.val • (x : R ⧸ K) = 0
    rw [← ha]
    change Ideal.Quotient.mk K (r.val * a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ (Ideal.mul_mem_mul r.property haJ))
  let : Module (R ⧸ I) p.ker := ht.module
  let : Field (R ⧸ I) := Ideal.Quotient.field I
  exact lTensor_injective_of_exact f p.ker.subtype p Subtype.val_injective hp
    p.exact_subtype_ker_map (lTensor_injective_of_baseChange (A := R ⧸ I) f hI) hJ

/-- Residual injectivity holds modulo `J + I^n` for every base ideal `J ≤ I`.
The flatness assumption is on the original target, not on a quotient target. -/
theorem lTensor_quotient_sup_pow_injective [Flat R M] (I J : Ideal R) [I.IsMaximal]
    (hJI : J ≤ I) (f : N →ₗ[R] M)
    (hf : Function.Injective (f.lTensor (R ⧸ I))) (n : ℕ) :
    Function.Injective (f.lTensor (R ⧸ (J ⊔ I ^ (n + 1)))) := by
  induction n with
  | zero =>
    have h : J ⊔ I ^ (0 + 1) = I := by rw [pow_one, sup_eq_right.mpr hJI]
    rw [h]
    exact hf
  | succ n ih =>
    apply lTensor_quotient_injective_step I (J ⊔ I ^ (n + 1)) _
      (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_succ _)) _) ?_ f hf ih
    rw [Ideal.mul_sup, ← pow_succ']
    exact sup_le (Ideal.mul_le_right.trans le_sup_left) le_sup_right

end Module.Flat

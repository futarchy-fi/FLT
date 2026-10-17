/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PairedCokernelElimination
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Residual errors after boundary elimination

A surjective boundary block permits testing ambient residual vanishing in the
mixed quotient. The remaining correction is still in the exact boundary
kernel; only its mixed discrepancy is allowed to differ by the scalar ideal.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PairedCokernel
variable {R A B C : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] (b : A →ₗ[R] B) (d : A →ₗ[R] C)
  (hb : Function.Surjective b) (J : Ideal R)

include hb in
/-- An isomorphism preserves scalar-ideal multiples of the whole module. -/
theorem inclusion_mem_smul_top_iff (x : C ⧸ (LinearMap.ker b).map d) :
    inclusion b d x ∈ J • (⊤ : Submodule R ((B × C) ⧸ LinearMap.range (b.prod d))) ↔
      x ∈ J • (⊤ : Submodule R (C ⧸ (LinearMap.ker b).map d)) := by
  have h := Submodule.comap_smul_top_of_surjective J (inclusion b d)
    (inclusion_surjective b d hb)
  rw [LinearMap.ker_eq_bot.mpr (inclusion_injective b d), sup_bot_eq] at h
  exact SetLike.ext_iff.mp h x

/-- Residual membership in a quotient is membership in the sum with its defining submodule. -/
theorem mk_mem_smul_top_iff (Q : Submodule R C) (c : C) :
    Q.mkQ c ∈ J • (⊤ : Submodule R (C ⧸ Q)) ↔
      c ∈ J • (⊤ : Submodule R C) ⊔ Q := by
  have h := Submodule.comap_smul_top_of_surjective J Q.mkQ Q.mkQ_surjective
  rw [Submodule.ker_mkQ] at h
  exact SetLike.ext_iff.mp h c

include hb in
/-- An actual boundary lift reduces the residual test to its full mixed discrepancy. -/
theorem boundary_mem_smul_top_iff (a : A) :
    (LinearMap.range (b.prod d)).mkQ (b a, 0) ∈
        J • (⊤ : Submodule R ((B × C) ⧸ LinearMap.range (b.prod d))) ↔
      d a ∈ J • (⊤ : Submodule R C) ⊔ (LinearMap.ker b).map d := by
  rw [← representative b d a 0, inclusion_mem_smul_top_iff b d hb J,
    mk_mem_smul_top_iff, zero_sub, Submodule.neg_mem_iff]

include hb in
/-- Residual vanishing constructs an exact boundary-kernel correction modulo the scalar ideal. -/
theorem boundary_mem_smul_top_iff_correction (a : A) :
    (LinearMap.range (b.prod d)).mkQ (b a, 0) ∈
        J • (⊤ : Submodule R ((B × C) ⧸ LinearMap.range (b.prod d))) ↔
      ∃ z : A, b z = 0 ∧ d a - d z ∈ J • (⊤ : Submodule R C) := by
  rw [boundary_mem_smul_top_iff b d hb J]
  constructor
  · intro h
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨z, hz, ?_⟩
    rw [← hxy, add_sub_cancel_right]
    exact hx
  · rintro ⟨z, hz, he⟩
    exact Submodule.mem_sup.mpr
      ⟨d a - d z, he, d z, ⟨z, hz, rfl⟩, sub_add_cancel _ _⟩

end FLT.Mazur.PairedCokernel

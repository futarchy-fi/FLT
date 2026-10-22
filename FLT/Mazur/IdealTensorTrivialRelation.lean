/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealTensorTransition
public import FLT.Mazur.RingFlatRelation

/-!
# Trivial relation certificates kill actual ideal tensors

The finite equation witnesses used in filtered descent annihilate tensors
in the extended ideal itself, rather than just their images in the algebra.
-/

@[expose] public noncomputable section
open TensorProduct
open scoped BigOperators
namespace FLT.Mazur.IdealTensorKernel
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- A trivial relation between ideal elements vanishes already in the tensor module. -/
theorem sum_tmul_eq_zero_of_trivial {K : Type*} [Fintype K]
    (I : Ideal R) (a : K → I) (x : K → S)
    (h : RingFlatRelation.Trivial (algebraMap R S) (fun k ↦ (a k).val) x) :
    ∑ k, x k ⊗ₜ[R] a k = 0 := by
  obtain ⟨n, b, y, hx, hb⟩ := h
  have hz (j : Fin n) : ∑ k, b k j • a k = 0 := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul,
      ZeroMemClass.coe_zero, mul_comm] using hb j
  calc
    ∑ k, x k ⊗ₜ[R] a k = ∑ k, ∑ j, y j ⊗ₜ[R] (b k j • a k) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hx k, sum_tmul]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Algebra.smul_def, smul_tmul, tmul_smul]
    _ = ∑ j, y j ⊗ₜ[R] (∑ k, b k j • a k) := by
      rw [Finset.sum_comm]
      simp only [tmul_sum]
    _ = 0 := by simp only [hz, tmul_zero, Finset.sum_const_zero]

end FLT.Mazur.IdealTensorKernel

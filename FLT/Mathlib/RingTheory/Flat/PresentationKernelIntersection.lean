/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.Operations

/-! # Flat targets give the kernel intersection needed to lift fibre relations -/

@[expose] public noncomputable section

namespace AlgHom

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [Module.Flat R A]
  (f : S →ₐ[R] A) (hf : Function.Surjective f) (J : Ideal R)

include hf

/-- A base-ideal linear combination vanishing in a flat target can be rewritten
using coefficients in the same base ideal and vectors in the original kernel. -/
theorem sum_mem_mul_ker_of_flat {ι : Type*} [Fintype ι]
    (r : ι → R) (hr : ∀ i, r i ∈ J) (s : ι → S)
    (hs : f (∑ i, r i • s i) = 0) :
    (∑ i, r i • s i) ∈ J.map (algebraMap R S) * RingHom.ker f := by
  classical
  have hrel : ∑ i, r i • f (s i) = 0 := by simpa only [map_sum, map_smul] using hs
  obtain ⟨n, c, y, hy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  choose z hz using fun j ↦ hf (y j)
  let t := fun i ↦ s i - ∑ j, c i j • z j
  have ht (i) : t i ∈ RingHom.ker f := by
    change f (s i - ∑ j, c i j • z j) = 0
    simp only [map_sub, map_sum, map_smul, hz, ← hy, sub_self]
  have hzero : ∑ i, r i • (∑ j, c i j • z j) = 0 := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hc, zero_smul, Finset.sum_const_zero]
  have heq : ∑ i, r i • t i = ∑ i, r i • s i := by
    simp only [t, smul_sub, Finset.sum_sub_distrib, hzero, sub_zero]
  rw [← heq]
  apply Submodule.sum_mem
  intro i _
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hr i)) (ht i)

/-- The original presentation kernel intersects each extended base ideal in its
product with that ideal. Only the target's base-flatness is used. -/
theorem ker_inf_map_eq_mul_of_flat :
    RingHom.ker f ⊓ J.map (algebraMap R S) = J.map (algebraMap R S) * RingHom.ker f := by
  classical
  apply le_antisymm _ (le_inf Ideal.mul_le_right Ideal.mul_le_left)
  intro s hs
  obtain ⟨c, t, ht, _, heq⟩ :=
    Submodule.mem_span_iff_exists_finset_subset.mp hs.2
  choose r hr hre using fun i : t ↦ ht i.property
  have heq' : ∑ i : t, r i • c i = s := by
    rw [← heq]
    rw [show (∑ a ∈ t, c a • a) = ∑ i : t, c i • (i : S) from
      (Finset.sum_coe_sort t (fun a ↦ c a • a)).symm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Algebra.smul_def, hre, smul_eq_mul, mul_comm]
  rw [← heq']
  exact f.sum_mem_mul_ker_of_flat hf J r hr (fun i ↦ c i) (by rw [heq']; exact hs.1)

end AlgHom

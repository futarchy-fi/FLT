/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolynomialTensorSplitFrame
public import FLT.Mazur.FiniteCoefficientDifferenceIdeal

/-!
# Complete split frames have comaximal endpoint difference ideals

The idempotents of a full product decomposition separate every pair of
coordinates over arbitrary test rings. Tensor induction brings this
separation back to differences of actual original source coefficients.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.PolynomialTensorSplitFrame
open FiniteCoefficientDifference
set_option backward.isDefEq.respectTransparency false
variable {R B T I : Type*} [CommRing R] [CommRing B] [CommRing T]
  [Algebra R B] [Algebra R T]
  (e : (T ⊗[R] B) ≃ₐ[T] (I → T))

/-- Complete-frame coordinates preserve the prescribed original scalar structure. -/
def coordinateAlgHom (i : I) : B →ₐ[R] T :=
  { coordinate e i with
    commutes' r := by
      change e (1 ⊗ₜ[R] algebraMap R B r) i = algebraMap R T r
      rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
      change e (algebraMap T (T ⊗[R] B) (algebraMap R T r)) i = _
      rw [e.commutes]
      rfl }

/-- The algebra-coordinate wrapper has the unchanged underlying ring map. -/
theorem coordinateAlgHom_toRingHom (i : I) :
    (coordinateAlgHom e i).toRingHom = coordinate e i := rfl

/-- The original full difference ideals of distinct coordinates are comaximal. -/
theorem differenceIdeal_pairwise_coprime (y : B →+* T) :
    Pairwise fun i j ↦ IsCoprime (differenceIdeal (coordinate e i) y)
      (differenceIdeal (coordinate e j) y) := by
  classical
  intro i j hij
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
  let K := differenceIdeal (coordinate e i) y ⊔ differenceIdeal (coordinate e j) y
  have hmem : ∀ z : T ⊗[R] B, e z i - e z j ∈ K := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add z w hz hw =>
      simpa only [map_add, Pi.add_apply, add_sub_add_comm] using K.add_mem hz hw
    | tmul t b =>
      have hi : coordinate e i b - y b ∈ K :=
        Ideal.mem_sup_left (Ideal.subset_span (Set.mem_range_self b))
      have hj : coordinate e j b - y b ∈ K :=
        Ideal.mem_sup_right (Ideal.subset_span (Set.mem_range_self b))
      have hd : coordinate e i b - coordinate e j b ∈ K := by
        simpa only [sub_sub_sub_cancel_right] using K.sub_mem hi hj
      have ht : t ⊗ₜ[R] b = t • (1 ⊗ₜ[R] b) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ht, map_smul]
      change t * coordinate e i b - t * coordinate e j b ∈ K
      rw [← mul_sub]
      exact K.mul_mem_left t hd
  have h := hmem (e.symm (Pi.single i 1))
  simpa only [e.apply_symm_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij.symm,
    sub_zero] using h

end FLT.Mazur.PolynomialTensorSplitFrame

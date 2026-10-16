/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Descent of a prescribed linear lifting problem

A lift of the pure tensor of one prescribed section descends through a
faithfully flat algebra. Injectivity on the cokernel suffices; the chosen
tensor lift need not itself be a pure tensor or satisfy a descent datum.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FaithfullyFlatSectionLift
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
  (S : Type*) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]

/-- Membership of a prescribed section in a linear image is detected after faithful flatness. -/
theorem exists_lift_iff (y : N) :
    (∃ x : S ⊗[R] M, f.lTensor S x = 1 ⊗ₜ[R] y) ↔ ∃ x : M, f x = y := by
  constructor
  · rintro ⟨x, hx⟩
    have hz : (1 : S) ⊗ₜ[R] f.range.mkQ y = 0 := by
      rw [← LinearMap.lTensor_tmul, ← hx, ← LinearMap.comp_apply,
        ← LinearMap.lTensor_comp]
      rw [(LinearMap.exact_map_mkQ_range f).linearMap_comp_eq_zero,
        LinearMap.lTensor_zero, LinearMap.zero_apply]
    have hy : f.range.mkQ y = 0 := by
      apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := S) (N ⧸ f.range)
      simpa only [TensorProduct.mk_apply, TensorProduct.tmul_zero] using hz
    exact (LinearMap.exact_map_mkQ_range f y).mp hy
  · rintro ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ[R] x, rfl⟩

/-- The complete original range is recovered by contracting the extended range. -/
theorem comap_tensor_range :
    (f.lTensor S).range.comap (TensorProduct.mk R S N 1) = f.range := by
  ext y
  exact exists_lift_iff f S y

/-- Several prescribed equations may be descended together by using one product target. -/
theorem exists_pair_lift_iff {P : Type*} [AddCommGroup P] [Module R P]
    (g : M →ₗ[R] P) (y : N) (z : P) :
    (∃ x : S ⊗[R] M, (f.prod g).lTensor S x = 1 ⊗ₜ[R] (y, z)) ↔
      ∃ x : M, f x = y ∧ g x = z := by
  rw [exists_lift_iff]
  change (∃ x, (f x, g x) = (y, z)) ↔ _
  simp only [Prod.mk.injEq]

end FLT.Mazur.FaithfullyFlatSectionLift

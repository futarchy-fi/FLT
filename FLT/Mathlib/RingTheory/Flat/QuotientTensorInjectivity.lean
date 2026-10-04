/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Operations

/-! # Tensor injectivity modulo an ideal as a membership criterion -/

@[expose] public section

open TensorProduct

namespace LinearMap

variable {R N M : Type*} [CommRing R]
  [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]

/-- Tensor injectivity modulo an ideal means that the map reflects membership
in the corresponding ideal multiples. -/
theorem lTensor_quotient_injective_iff (f : N →ₗ[R] M) (I : Ideal R) :
    Function.Injective (f.lTensor (R ⧸ I)) ↔
      ∀ x : N, f x ∈ I • (⊤ : Submodule R M) → x ∈ I • (⊤ : Submodule R N) := by
  have zero_iff (x : N) : (1 : R ⧸ I) ⊗ₜ[R] x = 0 ↔ x ∈ I • (⊤ : Submodule R N) := by
    rw [← (quotTensorEquivQuotSMul N I).map_eq_zero_iff]
    simp
  have zero_iff' (x : M) : (1 : R ⧸ I) ⊗ₜ[R] x = 0 ↔ x ∈ I • (⊤ : Submodule R M) := by
    rw [← (quotTensorEquivQuotSMul M I).map_eq_zero_iff]
    simp
  constructor
  · intro h x hx
    apply (zero_iff x).mp
    apply h
    simpa only [lTensor_tmul, map_zero] using (zero_iff' (f x)).mpr hx
  · intro h
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro z hz
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (quotTensorEquivQuotSMul N I z)
    have hz' : z = (1 : R ⧸ I) ⊗ₜ[R] x := by
      apply (quotTensorEquivQuotSMul N I).injective
      simpa using hx.symm
    rw [hz'] at hz ⊢
    apply (zero_iff x).mpr
    apply h
    apply (zero_iff' (f x)).mp
    exact hz

end LinearMap

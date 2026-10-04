/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic

/-! # The first two module-valued Amitsur differentials -/

@[expose] public noncomputable section
open TensorProduct
namespace Algebra.Amitsur
variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- Insert the unit of the cover as the first tensor factor. -/
def unit : M →ₗ[R] S ⊗[R] M := TensorProduct.mk R S M 1

/-- The degree-zero coboundary, with the unit-insertion sign convention. -/
def d₀ : S ⊗[R] M →ₗ[R] S ⊗[R] (S ⊗[R] M) :=
  unit R S (S ⊗[R] M) - (unit R S M).lTensor S

/-- The degree-one coboundary on actual triple tensors. -/
def d₁ : S ⊗[R] (S ⊗[R] M) →ₗ[R] S ⊗[R] (S ⊗[R] (S ⊗[R] M)) :=
  unit R S (S ⊗[R] (S ⊗[R] M)) - (unit R S (S ⊗[R] M)).lTensor S +
    ((unit R S M).lTensor S).lTensor S

/-- Evaluation of the degree-zero map. -/
theorem d₀_tmul (s : S) (m : M) :
    d₀ R S M (s ⊗ₜ[R] m) =
      1 ⊗ₜ[R] (s ⊗ₜ[R] m) - s ⊗ₜ[R] (1 ⊗ₜ[R] m) := rfl

/-- Evaluation of the degree-one map. -/
theorem d₁_tmul (s t : S) (m : M) :
    d₁ R S M (s ⊗ₜ[R] (t ⊗ₜ[R] m)) =
      1 ⊗ₜ[R] (s ⊗ₜ[R] (t ⊗ₜ[R] m)) -
      s ⊗ₜ[R] (1 ⊗ₜ[R] (t ⊗ₜ[R] m)) +
      s ⊗ₜ[R] (t ⊗ₜ[R] (1 ⊗ₜ[R] m)) := rfl

/-- Every coboundary satisfies the degree-one cocycle equation. -/
theorem d₁_comp_d₀ : (d₁ R S M).comp (d₀ R S M) = 0 := by
  ext s m
  change d₁ R S M (d₀ R S M (s ⊗ₜ[R] m)) = 0
  simp only [d₀_tmul, map_sub, d₁_tmul]
  abel

end Algebra.Amitsur

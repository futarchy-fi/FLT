/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.AmitsurDegreeOneMaps
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Multiplication contracts the base-changed Amitsur complex -/

@[expose] public noncomputable section
open TensorProduct
namespace Algebra.Amitsur
variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- Multiply the first two factors of a base-changed cochain. -/
def contraction : S ⊗[R] (S ⊗[R] M) →ₗ[R] S ⊗[R] M :=
  (LinearMap.mul' R S).rTensor M ∘ₗ
    (_root_.TensorProduct.assoc R S S M).symm.toLinearMap

/-- The contraction uses the original multiplication in the cover. -/
theorem contraction_tmul (s t : S) (m : M) :
    contraction R S M (s ⊗ₜ[R] (t ⊗ₜ[R] m)) = (s * t) ⊗ₜ[R] m := rfl

/-- Multiplication gives a degree-one contracting homotopy after tensoring with the cover. -/
theorem contraction_d₁ :
    (contraction R S (S ⊗[R] (S ⊗[R] M))).comp ((d₁ R S M).lTensor S) =
      LinearMap.id - ((d₀ R S M).lTensor S).comp
        (contraction R S (S ⊗[R] M)) := by
  ext s t u m
  change contraction R S (S ⊗[R] (S ⊗[R] M))
    ((d₁ R S M).lTensor S (s ⊗ₜ[R] (t ⊗ₜ[R] (u ⊗ₜ[R] m)))) =
    s ⊗ₜ[R] (t ⊗ₜ[R] (u ⊗ₜ[R] m)) -
      (d₀ R S M).lTensor S
        (contraction R S (S ⊗[R] M) (s ⊗ₜ[R] (t ⊗ₜ[R] (u ⊗ₜ[R] m))))
  simp only [LinearMap.lTensor_tmul, d₁_tmul,
    tmul_add, tmul_sub, map_add, map_sub, contraction_tmul, mul_one,
    d₀_tmul]
  abel

/-- A base-changed cocycle is the coboundary of its explicit multiplication contraction. -/
theorem baseChanged_cocycle_correction
    (z : S ⊗[R] (S ⊗[R] (S ⊗[R] M)))
    (hz : (d₁ R S M).lTensor S z = 0) :
    (d₀ R S M).lTensor S (contraction R S (S ⊗[R] M) z) = z := by
  have h := LinearMap.congr_fun (contraction_d₁ R S M) z
  simp only [LinearMap.comp_apply, hz, map_zero, LinearMap.sub_apply,
    LinearMap.id_apply] at h
  exact (sub_eq_zero.mp h.symm).symm

/-- The degree-one complex becomes exact after tensoring with its algebra. -/
theorem baseChanged_exact :
    Function.Exact ((d₀ R S M).lTensor S) ((d₁ R S M).lTensor S) := by
  intro z
  constructor
  · intro hz
    exact ⟨contraction R S (S ⊗[R] M) z, baseChanged_cocycle_correction R S M z hz⟩
  · rintro ⟨w, rfl⟩
    have h : ((d₁ R S M).lTensor S).comp ((d₀ R S M).lTensor S) = 0 := by
      rw [← LinearMap.lTensor_comp, d₁_comp_d₀, LinearMap.lTensor_zero]
    exact LinearMap.congr_fun h w

end Algebra.Amitsur

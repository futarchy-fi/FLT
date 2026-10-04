/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.AdicGradedTensorComparison
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-! # The exact sequence between successive adic quotients -/

@[expose] public noncomputable section

namespace Ideal

variable {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)

/-- Inclusion of the adic graded piece into the next quotient. -/
def adicGradedι : I.AdicGradedPiece n →ₗ[R] R ⧸ I ^ (n + 1) :=
  ((I ^ n).map (Ideal.Quotient.mk (I ^ (n + 1)))).subtype.restrictScalars R ∘ₗ
    (I.powQuotPowSuccLinearEquivMapMkPowSuccPow n).toLinearMap

@[simp]
theorem adicGradedι_mk (x : (I ^ n : Ideal R)) :
    I.adicGradedι n (Submodule.Quotient.mk x) = Ideal.Quotient.mk (I ^ (n + 1)) x := rfl

/-- The graded inclusion is injective before any tensoring. -/
theorem adicGradedι_injective : Function.Injective (I.adicGradedι n) :=
  Subtype.val_injective.comp (I.powQuotPowSuccLinearEquivMapMkPowSuccPow n).injective

/-- The transition in the adic tower as an `R`-linear map. -/
abbrev adicQuotientπ : (R ⧸ I ^ (n + 1)) →ₗ[R] R ⧸ I ^ n :=
  Submodule.factor (Ideal.pow_le_pow_right (Nat.le_succ n))

/-- The graded term is precisely the kernel of the adic transition. -/
theorem adicQuotient_exact : Function.Exact (I.adicGradedι n) (I.adicQuotientπ n) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  constructor
  · intro hx
    have hx' : x ∈ I ^ n := Ideal.Quotient.eq_zero_iff_mem.mp hx
    exact ⟨Submodule.Quotient.mk ⟨x, hx'⟩, rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← hy]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr y.property

/-- Adic transitions are surjective. -/
theorem adicQuotientπ_surjective : Function.Surjective (I.adicQuotientπ n) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk _ x, rfl⟩

variable (M : Type*) [AddCommGroup M] [Module R M]

/-- Tensoring the adic row is right exact for every module. -/
theorem adicQuotient_rTensor_exact :
    Function.Exact ((I.adicGradedι n).rTensor M) ((I.adicQuotientπ n).rTensor M) :=
  rTensor_exact M (I.adicQuotient_exact n) (I.adicQuotientπ_surjective n)

/-- A flat module makes the left end of the tensor adic row injective. -/
theorem adicGradedι_rTensor_injective [Module.Flat R M] :
    Function.Injective ((I.adicGradedι n).rTensor M) :=
  Module.Flat.rTensor_preserves_injective_linearMap _ (I.adicGradedι_injective n)

end Ideal

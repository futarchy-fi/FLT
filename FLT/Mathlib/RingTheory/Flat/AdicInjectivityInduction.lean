/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.AdicQuotientExactRow
public import FLT.Mathlib.RingTheory.Flat.TensorInjectivityExtension
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Residual injectivity implies injectivity modulo every adic power -/

@[expose] public noncomputable section

namespace Module.Flat

variable {R N M : Type*} [CommRing R]
  [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]

/-- A map into a flat module which is injective modulo a maximal ideal remains
injective modulo every positive power of that ideal. -/
theorem lTensor_quotient_pow_injective [Flat R M] (I : Ideal R) [I.IsMaximal]
    (f : N →ₗ[R] M) (hf : Function.Injective (f.lTensor (R ⧸ I))) (n : ℕ) :
    Function.Injective (f.lTensor (R ⧸ I ^ (n + 1))) := by
  let : Field (R ⧸ I) := Ideal.Quotient.field I
  induction n with
  | zero =>
    have h : I ^ (0 + 1) = I := pow_one I
    rw [h]
    exact hf
  | succ n ih =>
    apply lTensor_injective_of_exact f (I.adicGradedι (n + 1)) (I.adicQuotientπ (n + 1))
      (I.adicGradedι_injective _) (I.adicQuotientπ_surjective _) (I.adicQuotient_exact _)
      ?_ ih
    exact lTensor_injective_of_baseChange (A := R ⧸ I) f hf

end Module.Flat

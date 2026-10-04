/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Identifying the actual base change from a reduction kernel

A surjective reduction with the expected extended kernel gives the actual tensor
base change, without flatness hypotheses.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace AlgHom
variable {B C D E : Type*} [CommRing B] [CommRing C] [CommRing D] [CommRing E]
  [Algebra B C] [Algebra B D] [Algebra B E]

/-- A surjective map with the expected coefficient kernel identifies its target with
base change to the coefficient quotient. -/
def reductionBaseChangeEquiv (hq : Function.Surjective (algebraMap B C))
    (t : D →ₐ[B] E) (ht : Function.Surjective t)
    (hker : RingHom.ker t = (RingHom.ker (algebraMap B C)).map (algebraMap B D)) :
    (D ⊗[B] C) ≃ₐ[B] E :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : D ≃ₐ[B] D)
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId B C) hq).symm).trans
    (((Algebra.TensorProduct.quotIdealMapEquivTensorQuot D
      (RingHom.ker (algebraMap B C))).restrictScalars B).symm.trans
      ((Ideal.quotientEquivAlgOfEq B hker.symm).trans
        (Ideal.quotientKerAlgEquivOfSurjective ht)))

/-- The base-change identification preserves the original reduction of each lifted element. -/
@[simp]
theorem reductionBaseChangeEquiv_tmul_one (hq : Function.Surjective (algebraMap B C))
    (t : D →ₐ[B] E) (ht : Function.Surjective t)
    (hker : RingHom.ker t = (RingHom.ker (algebraMap B C)).map (algebraMap B D))
    (d : D) : reductionBaseChangeEquiv hq t ht hker (d ⊗ₜ[B] (1 : C)) = t d := by
  change Ideal.quotientKerAlgEquivOfSurjective ht
    (Ideal.quotientEquivAlgOfEq B hker.symm
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot D _).symm
        (d ⊗ₜ[B] (Ideal.quotientKerAlgEquivOfSurjective
          (f := Algebra.ofId B C) hq).symm 1))) = t d
  rw [map_one]
  change t ((1 : B) • d) = t d
  rw [one_smul]

end AlgHom

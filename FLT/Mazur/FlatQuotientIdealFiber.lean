/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorKernelFlatCokernel
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Ideal fibers with a flat quotient

Flatness of the quotient, rather than flatness of the coefficient change,
makes the ideal inclusion remain injective. Thus the tensor of the ideal
identifies with the actual extended ideal, including residue-field fibers.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FCurve

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- A flat ambient and a flat quotient give a flat ideal over the base ring. -/
theorem ideal_flat_of_flat_quotient (I : Ideal B)
    [Module.Flat R B] [Module.Flat R (B ⧸ I)] : Module.Flat R I :=
  TensorKernelFlatCokernel.flat_kernel_of_shortExact
    (I.subtype.restrictScalars R) (I.mkQ.restrictScalars R)
    I.subtype_injective I.mkQ_surjective (LinearMap.exact_subtype_mkQ I)

/-- The ideal inclusion remains injective for arbitrary coefficient modules. -/
theorem ideal_fiber_inclusion_injective (I : Ideal B) [Module.Flat R (B ⧸ I)]
    (M : Type*) [AddCommGroup M] [Module R M] :
    Function.Injective ((I.subtype.restrictScalars R).lTensor M) :=
  LinearMap.lTensor_injective_of_exact_of_flat (I.mkQ.restrictScalars R)
    I.mkQ_surjective (I.subtype.restrictScalars R) I.subtype_injective
    (LinearMap.exact_subtype_mkQ I) M

/-- The tensor ideal is the actual ideal in every coefficient fiber. -/
def flatQuotientIdealFiberEquiv (I : Ideal B) [Module.Flat R (B ⧸ I)]
    (C : Type*) [CommRing C] [Algebra R C] :
    C ⊗[R] I ≃ₗ[C]
      (I.map (Algebra.TensorProduct.includeRight (R := R) (A := C))).restrictScalars C :=
  (LinearEquiv.ofInjective
    (AlgebraTensorModule.lTensor C C (I.subtype.restrictScalars R))
    (ideal_fiber_inclusion_injective I C)).trans
      (LinearEquiv.ofEq _ _ (AlgebraTensorModule.range_lTensor_idealMap _ _ _))

/-- The comparison retains the actual inclusion on pure tensors. -/
@[simp]
theorem flatQuotientIdealFiberEquiv_tmul (I : Ideal B) [Module.Flat R (B ⧸ I)]
    (C : Type*) [CommRing C] [Algebra R C] (c : C) (x : I) :
    (flatQuotientIdealFiberEquiv I C (c ⊗ₜ[R] x)).val = c ⊗ₜ[R] (x : B) := rfl

end FLT.Mazur.FCurve

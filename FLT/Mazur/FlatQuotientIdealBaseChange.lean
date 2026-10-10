/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatIdealTensor
public import FLT.Mazur.FlatQuotientIdealFiber

/-!
# Finite presentation of ideals under coefficient change

A flat quotient makes the ideal inclusion stay injective under any change of
coefficients. The resulting ideal is the tensor extension as a module over
the ambient algebra, so finite presentation survives without flatness of the
coefficient change.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FCurve
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable (C : Type*) [CommRing C] [Algebra R C]

/-- Cancel the ambient scalar extension before changing coefficients. -/
def idealCoefficientTensorCancel (I : Ideal B) :
    (B ⊗[R] C) ⊗[B] I ≃ₗ[B] I ⊗[R] C :=
  TensorProduct.comm B (B ⊗[R] C) I ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange R B B I C

/-- Flatness of the quotient ensures injectivity of the ambient tensor inclusion. -/
theorem idealTensorInclusion_injective_of_flat_quotient (I : Ideal B)
    [Module.Flat R (B ⧸ I)] :
    Function.Injective (idealTensorInclusion (S := B ⊗[R] C) I) := by
  have he : (idealTensorInclusion (S := B ⊗[R] C) I).restrictScalars R =
      ((I.subtype.restrictScalars R).rTensor C).comp
        ((idealCoefficientTensorCancel C I).toLinearMap.restrictScalars R) := by
    apply LinearMap.ext
    intro z
    induction z with
    | add z t hz ht => simp only [map_add, hz, ht]
    | tmul z x =>
      induction z with
      | add z t hz ht => simp only [add_tmul, map_add, hz, ht]
      | tmul b c =>
        simp only [LinearMap.restrictScalars_apply, idealTensorInclusion_tmul,
          LinearMap.comp_apply, idealCoefficientTensorCancel, LinearEquiv.coe_toLinearMap,
          LinearEquiv.trans_apply, TensorProduct.comm_tmul,
          AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.rTensor_tmul]
        change (b ⊗ₜ[R] c) * (x.val ⊗ₜ[R] (1 : C)) = (b * x.val) ⊗ₜ[R] c
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have hi : Function.Injective ((I.subtype.restrictScalars R).rTensor C) := by
    intro x y h
    apply (TensorProduct.comm R I C).injective
    apply ideal_fiber_inclusion_injective I C
    simpa only [LinearMap.lTensor_comm] using congrArg (TensorProduct.comm R B C) h
  change Function.Injective ((idealTensorInclusion (S := B ⊗[R] C) I).restrictScalars R)
  rw [he]
  exact hi.comp (idealCoefficientTensorCancel C I).injective

/-- The full extended ideal is ambient scalar extension when the quotient is flat. -/
def flatQuotientIdealBaseChangeEquiv (I : Ideal B) [Module.Flat R (B ⧸ I)] :
    (B ⊗[R] C) ⊗[B] I ≃ₗ[B ⊗[R] C] I.map (algebraMap B (B ⊗[R] C)) :=
  (LinearEquiv.ofInjective (idealTensorInclusion I)
    (idealTensorInclusion_injective_of_flat_quotient C I)).trans
      (LinearEquiv.ofEq _ _ (idealTensorInclusion_range I))

/-- Arbitrary coefficient change preserves finite presentation of a flat-quotient ideal. -/
theorem ideal_finitePresentation_coefficientChange (I : Ideal B)
    [Module.Flat R (B ⧸ I)] [Module.FinitePresentation B I] :
    Module.FinitePresentation (B ⊗[R] C) (I.map (algebraMap B (B ⊗[R] C))) :=
  Module.FinitePresentation.of_equiv (flatQuotientIdealBaseChangeEquiv C I)

end FLT.Mazur.FCurve

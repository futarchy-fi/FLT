/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorAlgebraSemilinearEquiv
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Etale.Kaehler

/-!
# Completed original H1 through localization

The actual localization theorem for first cotangent homology, together with
finite-module completion, transports H1 along a completion equivalence
that preserves the original affine-ring action.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicLocalizedH1Comparison

open TensorProduct

universe u

variable {R A L : Type u} [CommRing R] [CommRing A] [CommRing L]
  [Algebra R A] [Algebra A L] [Algebra R L] [IsScalarTower R A L]
  [IsNoetherianRing A] [IsNoetherianRing L]
  [Module.Finite A (Algebra.H1Cotangent R A)]
  (T : Submonoid A) [IsLocalization T L] (I : Ideal A) (J : Ideal L)
  (e : AdicCompletion I A ≃ₐ[A] AdicCompletion J L)

attribute [local instance] TensorAlgebraSemilinearEquiv.forwardInverse
  TensorAlgebraSemilinearEquiv.reverseInverse

include T in
omit [IsNoetherianRing A] [IsNoetherianRing L] in
/-- Original localized H1 is finite when original affine H1 is finite. -/
theorem finite : Module.Finite L (Algebra.H1Cotangent R L) :=
  Module.Finite.of_surjective (Algebra.tensorH1CotangentOfIsLocalization R L T).toLinearMap
    (Algebra.tensorH1CotangentOfIsLocalization R L T).surjective

/-- Completion of localized H1 is scalar extension of the original affine H1. -/
def tensorEquiv : (AdicCompletion J L ⊗[A] Algebra.H1Cotangent R A) ≃ₗ[
    AdicCompletion J L] AdicCompletion J (Algebra.H1Cotangent R L) := by
  let _ := finite (R := R) (L := L) T
  exact (AlgebraTensorModule.cancelBaseChange A L (AdicCompletion J L)
    (AdicCompletion J L) (Algebra.H1Cotangent R A)).symm ≪≫ₗ
      (Algebra.tensorH1CotangentOfIsLocalization R L T).baseChange L
        (AdicCompletion J L) _ _ ≪≫ₗ
      AdicCompletion.ofTensorProductEquivOfFiniteNoetherian J (Algebra.H1Cotangent R L)

/-- The completion comparison transports completed original H1 through the actual localization. -/
def equiv : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom)
    (AdicCompletion I (Algebra.H1Cotangent R A))
    (AdicCompletion J (Algebra.H1Cotangent R L)) :=
  ((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I
    (Algebra.H1Cotangent R A)).symm.trans
      (TensorAlgebraSemilinearEquiv.equiv e (Algebra.H1Cotangent R A))).trans
        (tensorEquiv (R := R) T J)

end FLT.Mazur.AdicLocalizedH1Comparison

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicSeparatedDifferentials
public import FLT.Mazur.DerivationAlgEquivTransport

/-!
# Comparing completed original cotangent maps through a formal equivalence

The original cotangent universal properties give the comparison for every
separated common target. Its formula retains the original universal derivatives.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicCotangentHomComparison

variable {R A B N : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [IsNoetherianRing A] [IsNoetherianRing B]
  [Module.Finite A Ω[A⁄R]] [Module.Finite B Ω[B⁄R]]
  (I : Ideal A) (J : Ideal B) [AddCommGroup N]
  [Module R N] [Module A N] [Module B N]
  [Module (AdicCompletion I A) N] [Module (AdicCompletion J B) N]
  [IsScalarTower R A N] [IsScalarTower R B N]
  [IsScalarTower R (AdicCompletion I A) N] [IsScalarTower R (AdicCompletion J B) N]
  [IsScalarTower A (AdicCompletion I A) N] [IsScalarTower B (AdicCompletion J B) N]
  [IsHausdorff I N] [IsHausdorff J N]
  (e : AdicCompletion I A ≃ₐ[R] AdicCompletion J B)
  (he : ∀ a (x : N), e a • x = a • x)

/-- A formal equivalence compares maps out of the two completed original cotangent modules. -/
def equiv :
    (AdicCompletion J Ω[B⁄R] →ₗ[AdicCompletion J B] N) ≃
      (AdicCompletion I Ω[A⁄R] →ₗ[AdicCompletion I A] N) :=
  (AdicSeparatedDifferentials.equiv J).trans
    ((DerivationAlgEquivTransport.equiv e he).trans (AdicSeparatedDifferentials.equiv I).symm)

/-- The comparison sends each original differential to the derivative of its formal image. -/
theorem equiv_of_D (f : AdicCompletion J Ω[B⁄R] →ₗ[AdicCompletion J B] N) (a : A) :
    equiv I J e he f (AdicCompletion.of I Ω[A⁄R] (KaehlerDifferential.D R A a)) =
      f (AdicDerivationFiltration.completion (KaehlerDifferential.D R B) J
        (e (AdicCompletion.of I A a))) := by
  change AdicSeparatedDifferentials.lift I _
    (AdicCompletion.of I Ω[A⁄R] (KaehlerDifferential.D R A a)) = _
  rw [AdicSeparatedDifferentials.lift_of_D]
  rfl

end FLT.Mazur.AdicCotangentHomComparison

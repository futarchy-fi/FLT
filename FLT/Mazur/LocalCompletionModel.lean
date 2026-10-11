/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalCompletionFaithfullyFlat

/-!
# Original local-ring action on a model of its completion

An algebra equivalence from the actual completion equips its target with
the actual local-ring action. This action retains the original base and is
faithfully flat, so a formal arithmetic model can detect local obstructions.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.LocalCompletionModel

variable {R A C : Type*} [CommRing R] [CommRing A] [CommRing C]
  [Algebra R A] [Algebra R C] [IsLocalRing A]
  (e : AdicCompletion (IsLocalRing.maximalIdeal A) A ≃ₐ[R] C)

/-- The original local ring acts through its canonical completion map and the given comparison. -/
def scalars : A →+* C :=
  e.toRingHom.comp (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))

/-- The action on the formal model preserves the original base coefficients. -/
theorem scalars_algebraMap (r : R) :
    scalars e (algebraMap R A r) = algebraMap R C r :=
  e.commutes r

/-- The specified original base action and local-ring action form a scalar tower. -/
theorem scalarTower :
    let _ := (scalars e).toAlgebra
    IsScalarTower R A C := by
  let _ := (scalars e).toAlgebra
  exact IsScalarTower.of_algebraMap_eq (fun r ↦ (scalars_algebraMap e r).symm)

/-- The completion comparison is also an equivalence over the actual local ring. -/
def localAlgebraEquivalence :
    let _ := (scalars e).toAlgebra
    AdicCompletion (IsLocalRing.maximalIdeal A) A ≃ₐ[A] C := by
  let _ := (scalars e).toAlgebra
  exact { e.toRingEquiv with commutes' := fun _ ↦ rfl }

/-- The arithmetic model is faithfully flat for its original local-ring action. -/
theorem faithfullyFlat [IsNoetherianRing A] :
    let _ := (scalars e).toAlgebra
    Module.FaithfullyFlat A C := by
  let _ := (scalars e).toAlgebra
  let _ := LocalCompletionFaithfullyFlat.faithfullyFlat A
  exact Module.FaithfullyFlat.of_linearEquiv A _ (localAlgebraEquivalence e).symm.toLinearEquiv

end FLT.Mazur.LocalCompletionModel

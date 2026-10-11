/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalCompletionModel

/-!
# Transporting completed modules to a local completion model

An equivalence from the actual local completion transports its modules to
the model ring while preserving the original local and relative actions.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.LocalCompletionModelModule

variable {R A C N : Type*} [CommRing R] [CommRing A] [CommRing C]
  [Algebra R A] [Algebra R C] [IsLocalRing A]
  (e : AdicCompletion (IsLocalRing.maximalIdeal A) A ≃ₐ[R] C)
  [AddCommGroup N] [Module (AdicCompletion (IsLocalRing.maximalIdeal A) A) N]

/-- Transport the completed-ring action through the inverse comparison. -/
@[instance_reducible] def modelModule : Module C N := Module.compHom N e.symm.toRingHom

/-- Transport retains the action of each element of the actual completion. -/
theorem modelModule_smul (a : AdicCompletion (IsLocalRing.maximalIdeal A) A) (x : N) :
    let _ := modelModule (N := N) e
    e a • x = a • x := by
  let _ := modelModule (N := N) e
  change e.symm (e a) • x = a • x
  rw [e.symm_apply_apply]

/-- The original local-ring action factors through the transported model action. -/
theorem scalarTower [Module A N]
    [IsScalarTower A (AdicCompletion (IsLocalRing.maximalIdeal A) A) N] :
    let _ := (LocalCompletionModel.scalars e).toAlgebra
    let _ := modelModule (N := N) e
    IsScalarTower A C N := by
  let _ := (LocalCompletionModel.scalars e).toAlgebra
  let _ := modelModule (N := N) e
  apply IsScalarTower.of_algebraMap_smul
  intro a x
  change e.symm (e (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) a)) • x =
    a • x
  rw [e.symm_apply_apply, algebraMap_smul]

/-- Transport retains the original relative base action. -/
theorem relativeScalarTower [Module R N]
    [IsScalarTower R (AdicCompletion (IsLocalRing.maximalIdeal A) A) N] :
    let _ := modelModule (N := N) e
    IsScalarTower R C N := by
  let _ := modelModule (N := N) e
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  change e.symm (algebraMap R C r) • x = r • x
  rw [e.symm.commutes, algebraMap_smul]

end FLT.Mazur.LocalCompletionModelModule

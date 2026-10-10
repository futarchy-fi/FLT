/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Completeness of finite modules over a complete Noetherian ring

The original completion map is the composite of tensoring the base-ring
completion equivalence with the finite-module completion comparison.
-/

@[expose] public noncomputable section

open TensorProduct

namespace FLT.Mazur.FiniteModuleAdicComplete

universe u

variable {R : Type u} [CommRing R] (J : Ideal R)
  (M : Type u) [AddCommGroup M] [Module R M] [IsAdicComplete J R]

/-- Base-ring completeness identifies a module with its completed-base tensor product. -/
def tensorEquiv : M ≃ₗ[R] AdicCompletion J R ⊗[R] M :=
  (TensorProduct.lid R M).symm.trans
    (TensorProduct.congr (AdicCompletion.ofLinearEquiv J R) (LinearEquiv.refl R M))

/-- This identification sends a vector to the original unit tensor. -/
lemma tensorEquiv_apply (x : M) :
    tensorEquiv J M x = (1 : AdicCompletion J R) ⊗ₜ[R] x := by
  change AdicCompletion.of J R 1 ⊗ₜ[R] x = 1 ⊗ₜ[R] x
  rfl

/-- The tensor comparison composed with base completeness is the original completion map. -/
lemma comparison_tensorEquiv (x : M) :
    AdicCompletion.ofTensorProduct J M (tensorEquiv J M x) =
      AdicCompletion.of J M x := by
  rw [tensorEquiv_apply, AdicCompletion.ofTensorProduct_tmul, one_smul]

/-- Every finite module over a complete Noetherian base has bijective completion map. -/
theorem of_bijective [IsNoetherianRing R] [Module.Finite R M] :
    Function.Bijective (AdicCompletion.of J M) := by
  have h := (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian J M).comp
    (tensorEquiv J M).bijective
  simpa only [Function.comp_def, comparison_tensorEquiv] using h

/-- Finite-module completeness follows from base-ring completeness and Noetherianity. -/
theorem isAdicComplete [IsNoetherianRing R] [Module.Finite R M] :
    IsAdicComplete J M :=
  AdicCompletion.of_bijective_iff.mp (of_bijective J M)

end FLT.Mazur.FiniteModuleAdicComplete

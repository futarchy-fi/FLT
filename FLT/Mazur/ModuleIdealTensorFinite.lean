/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealTensorKernelFinite

/-!
# Ideal tensors for modules finite over the target algebra

The module may be infinite over the base. Its ideal tensor and obstruction
are finite over the target algebra, as needed for the local flatness criterion.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ModuleIdealTensor
variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- Tensor the base ideal inclusion, retaining the target algebra action. -/
def inclusion (I : Ideal R) : M ⊗[R] I →ₗ[S] M :=
  (AlgebraTensorModule.rid R S M).toLinearMap ∘ₗ AlgebraTensorModule.lTensor S M I.subtype

@[simp]
lemma inclusion_tmul (I : Ideal R) (m : M) (a : I) :
    inclusion (S := S) I (m ⊗ₜ[R] a) = (a : R) • m := rfl

/-- Scalar associativity reduces finiteness to a tensor product over the target. -/
theorem tensor_finite [Module.Finite S M] (I : Ideal R) (hI : I.FG) :
    Module.Finite S (M ⊗[R] I) := by
  let _ : Module.Finite R I := Module.Finite.of_fg hI
  exact Module.Finite.equiv (AlgebraTensorModule.cancelBaseChange R S S M I)

/-- The full obstruction is finite over the Noetherian target, not necessarily over the base. -/
theorem kernel_finite [IsNoetherianRing S] [Module.Finite S M]
    (I : Ideal R) (hI : I.FG) :
    Module.Finite S (LinearMap.ker (inclusion (S := S) (M := M) I)) := by
  let _ := tensor_finite (S := S) (M := M) I hI
  infer_instance

/-- The algebra-valued map agrees with the original affine obstruction map. -/
theorem inclusion_self (I : Ideal R) :
    inclusion (S := S) (M := S) I = FCurve.idealTensorInclusion I := rfl

end FLT.Mazur.ModuleIdealTensor

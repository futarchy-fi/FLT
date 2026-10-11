/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LinearMapKernelTransport
public import FLT.Mazur.AdicFiniteModuleExt
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Completion commutes with kernels between finite modules

The finite-module tensor comparison identifies the completed kernel with
the kernel of the completed original differential.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicFiniteKernelEquiv

open TensorProduct

universe u

variable {R M N : Type u} [CommRing R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [Module.Finite R M]
  [AddCommGroup N] [Module R N] [Module.Finite R N]
  (I : Ideal R) (f : M →ₗ[R] N)

/-- Tensor completion transports the kernel of the scalar-extended original differential. -/
def tensorKernelEquiv : LinearMap.ker (f.baseChange (AdicCompletion I R)) ≃ₗ[
    AdicCompletion I R] LinearMap.ker (AdicCompletion.map I f) :=
  LinearMapKernelTransport.equiv _ _
    (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M)
    (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I N)
    (AdicCompletion.ofTensorProduct_naturality I f).symm

/-- The completion of an original kernel is the kernel of the completed original map. -/
def equiv : AdicCompletion I (LinearMap.ker f) ≃ₗ[AdicCompletion I R]
    LinearMap.ker (AdicCompletion.map I f) :=
  (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I (LinearMap.ker f)).symm ≪≫ₗ
    LinearMap.tensorKerEquiv (AdicCompletion I R) (AdicCompletion I R) f ≪≫ₗ
      tensorKernelEquiv I f

/-- Kernel completion retains the original inclusion on every original kernel element. -/
theorem equiv_of (x : LinearMap.ker f) :
    (equiv I f (AdicCompletion.of I (LinearMap.ker f) x)).val =
      AdicCompletion.of I M x.val := by
  change (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M)
    (LinearMap.tensorKerEquiv (AdicCompletion I R) (AdicCompletion I R) f
      ((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I (LinearMap.ker f)).symm
        (AdicCompletion.of I (LinearMap.ker f) x))).val = _
  simp [LinearMap.tensorKerEquiv_apply]

/-- On every completed element, the kernel equivalence is the completed original inclusion. -/
theorem equiv_val (x : AdicCompletion I (LinearMap.ker f)) :
    (equiv I f x).val = AdicCompletion.map I (LinearMap.ker f).subtype x := by
  have h : (LinearMap.ker (AdicCompletion.map I f)).subtype.comp (equiv I f).toLinearMap =
      AdicCompletion.map I (LinearMap.ker f).subtype := by
    apply AdicFiniteModuleExt.ext_of I
    intro y
    exact equiv_of I f y
  exact LinearMap.congr_fun h x

end FLT.Mazur.AdicFiniteKernelEquiv

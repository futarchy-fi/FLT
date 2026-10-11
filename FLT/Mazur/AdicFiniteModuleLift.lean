/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicFiniteModuleExt

/-!
# Extending linear maps from finite original modules

The finite Noetherian tensor comparison extends an original linear map
into a module over the completed ring. The extension is uniquely determined
by its values on original elements; no completeness assumption on the target
is needed for this linear construction.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicFiniteModuleLift

universe u

variable {A M : Type u} [CommRing A] [IsNoetherianRing A]
  [AddCommGroup M] [Module A M] [Module.Finite A M] (I : Ideal A)
  {N : Type*} [AddCommGroup N] [Module A N] [Module (AdicCompletion I A) N]
  [IsScalarTower A (AdicCompletion I A) N]

/-- Extend an original linear map using the actual finite-module tensor comparison. -/
def lift (f : M →ₗ[A] N) : AdicCompletion I M →ₗ[AdicCompletion I A] N :=
  (TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.lsmul (AdicCompletion I A) (M →ₗ[A] N)).flip f)).comp
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).symm.toLinearMap

/-- The extended map retains every original value. -/
@[simp] theorem lift_of (f : M →ₗ[A] N) (m : M) :
    lift I f (AdicCompletion.of I M m) = f m := by
  simp [lift]

/-- The extension is unique among completed-linear maps. -/
theorem lift_unique (f : M →ₗ[A] N) (g : AdicCompletion I M →ₗ[AdicCompletion I A] N)
    (h : ∀ m, g (AdicCompletion.of I M m) = f m) : g = lift I f := by
  apply AdicFiniteModuleExt.ext_of I
  intro m
  rw [h, lift_of]

/-- Restricting an extension along the original module recovers the original map. -/
@[simp] theorem lift_comp_of (f : M →ₗ[A] N) :
    (lift I f).restrictScalars A ∘ₗ AdicCompletion.of I M = f := by
  ext m
  exact lift_of I f m

end FLT.Mazur.AdicFiniteModuleLift

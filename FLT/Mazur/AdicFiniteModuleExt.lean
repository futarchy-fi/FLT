/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Original generators determine maps from finite module completions

For a finite original module, its original elements generate its completion
over the completed ring. Applied to original differentials, this gives an
extensionality principle using only differentials of original sections.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicFiniteModuleExt

open scoped TensorProduct

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  (I : Ideal A) [Module.Finite A M]
  {N : Type*} [AddCommGroup N] [Module (AdicCompletion I A) N]

/-- Original elements determine a completed-linear map from a finite module completion. -/
theorem ext_of (f g : AdicCompletion I M →ₗ[AdicCompletion I A] N)
    (h : ∀ m, f (AdicCompletion.of I M m) = g (AdicCompletion.of I M m)) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M x
  refine TensorProduct.inductionOn x ?_ ?_
  · intro a m
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul, map_smul, h]
  · intro x y hx hy
    simp only [map_add, hx, hy]

variable {R : Type*} [CommRing R] [Algebra R A] [Module.Finite A Ω[A⁄R]]

/-- Differentials of original sections determine maps from completed original differentials. -/
theorem ext_differentials
    (f g : AdicCompletion I Ω[A⁄R] →ₗ[AdicCompletion I A] N)
    (h : ∀ a, f (AdicCompletion.of I Ω[A⁄R] (KaehlerDifferential.D R A a)) =
      g (AdicCompletion.of I Ω[A⁄R] (KaehlerDifferential.D R A a))) : f = g := by
  let _ : Module A N := Module.compHom N (algebraMap A (AdicCompletion I A))
  let _ : IsScalarTower A (AdicCompletion I A) N := IsScalarTower.of_algebraMap_smul
    fun _ _ ↦ rfl
  let _ : Module R N := Module.compHom N (algebraMap R A)
  let _ : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  apply ext_of I
  have he : (f.restrictScalars A).comp (AdicCompletion.of I Ω[A⁄R]) =
      (g.restrictScalars A).comp (AdicCompletion.of I Ω[A⁄R]) := by
    apply Derivation.liftKaehlerDifferential_unique
    ext a
    exact h a
  exact fun m ↦ LinearMap.congr_fun he m

end FLT.Mazur.AdicFiniteModuleExt

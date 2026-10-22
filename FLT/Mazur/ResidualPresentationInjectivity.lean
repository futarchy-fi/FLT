/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ResidualPresentationKernel

/-!
# Propagating injectivity through a flat residual cokernel

If a presentation is injective after a first scalar extension and its
cokernel there is flat, it remains injective after every further extension.
The first extension itself need not be flat.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ResidualPresentationInjectivity
variable {R P N M : Type*} [CommRing R]
  [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
  [AddCommGroup M] [Module R M]
  (A B : Type*) [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- Residual injectivity and a flat residual cokernel control every later coefficient ring. -/
theorem baseChange_injective (f : P →ₗ[R] N) (q : N →ₗ[R] M)
    (he : Function.Exact f q) (hq : Function.Surjective q)
    [Module.Flat A (A ⊗[R] M)] (hf : Function.Injective (f.baseChange A)) :
    Function.Injective (f.baseChange B) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro z hz
  change z = 0
  obtain ⟨y, hy⟩ := ResidualPresentationKernel.exists_kernel_lift A B f q he hq z hz
  have hk : (f.baseChange A).ker.subtype = 0 := by
    ext x
    exact hf (x.property.trans (map_zero _).symm)
  rw [hk, LinearMap.baseChange_zero, LinearMap.zero_apply, map_zero] at hy
  exact hy.symm

end FLT.Mazur.ResidualPresentationInjectivity

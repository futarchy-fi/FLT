/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Flat.Basic

/-! # Passing tensor injectivity across an exact sequence -/

@[expose] public section

open TensorProduct

namespace Module.Flat

variable {R N M A B C : Type*} [CommRing R]
  [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

/-- If the target is flat, injectivity after tensoring the ends of a short
exact sequence implies injectivity after tensoring its middle term. -/
theorem lTensor_injective_of_exact [Flat R M] (f : N →ₗ[R] M)
    (i : A →ₗ[R] B) (p : B →ₗ[R] C) (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p)
    (hA : Function.Injective (f.lTensor A)) (hC : Function.Injective (f.lTensor C)) :
    Function.Injective (f.lTensor B) := by
  have comm_i : (i.rTensor M) ∘ₗ (f.lTensor A) = (f.lTensor B) ∘ₗ (i.rTensor N) := by
    ext; rfl
  have comm_p : (p.rTensor M) ∘ₗ (f.lTensor B) = (f.lTensor C) ∘ₗ (p.rTensor N) := by
    ext; rfl
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro z hz
  have hz' : f.lTensor B z = 0 := hz
  have hpz : p.rTensor N z = 0 := by
    apply hC
    rw [map_zero, ← LinearMap.comp_apply, ← comm_p]
    change p.rTensor M (f.lTensor B z) = 0
    rw [hz', map_zero]
  obtain ⟨y, hy⟩ := (_root_.rTensor_exact N hex hp z).mp hpz
  have hfy : f.lTensor A y = 0 := by
    apply Flat.rTensor_preserves_injective_linearMap (M := M) i hi
    rw [map_zero, ← LinearMap.comp_apply, comm_i]
    change f.lTensor B (i.rTensor N y) = 0
    rw [hy, hz']
  have hy0 : y = 0 := hA (by simpa using hfy)
  simpa [hy0] using hy.symm

end Module.Flat

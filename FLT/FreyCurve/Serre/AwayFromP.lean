/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep

/-!
# Unipotent inertia and the characters of the Serre bridge

The algebraic input for unramifiedness away from the torsion prime: if inertia acts
with `(ρ(σ) - 1)² = 0`, it acts trivially on every one-dimensional submodule and
quotient. The geometric assertion about inertia on semistable elliptic-curve torsion
is a separate input, not proved in this file.
-/

@[expose] public section

namespace Module.End
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- A square-unipotent endomorphism of the standard line is the identity. -/
theorem eq_one_of_sub_one_sq_eq_zero (a : Module.End k k)
    (ha : (a - 1) ^ 2 = 0) : a = 1 := by
  have hscalar (x : k) : a x = x * a 1 := by
    simpa using a.map_smul x (1 : k)
  have h := LinearMap.congr_fun ha 1
  change a (a 1 - 1) - (a 1 - 1) = 0 at h
  rw [hscalar (a 1 - 1)] at h
  have hzero : (a 1 - 1) * (a 1 - 1) = 0 := by
    calc
      _ = (a 1 - 1) * a 1 - (a 1 - 1) := by ring
      _ = 0 := h
  have hone : a 1 = 1 := sub_eq_zero.mp (mul_self_eq_zero.mp hzero)
  apply LinearMap.ext
  intro x
  change a x = x
  rw [hscalar x, hone, mul_one]

/-- A stable line in a square-unipotent module has trivial action. -/
theorem eq_one_of_injective_of_sub_one_sq_eq_zero (f : Module.End k V) (a : Module.End k k)
    (i : k →ₗ[k] V) (hi : Function.Injective i)
    (heq : ∀ x, f (i x) = i (a x)) (hf : (f - 1) ^ 2 = 0) : a = 1 := by
  apply eq_one_of_sub_one_sq_eq_zero
  apply LinearMap.ext
  intro x
  apply hi
  have h := LinearMap.congr_fun hf (i x)
  simpa only [pow_two, Module.End.mul_apply, LinearMap.sub_apply,
    Module.End.one_apply, map_sub, heq, map_zero, LinearMap.zero_apply] using h

/-- A one-dimensional quotient of a square-unipotent module has trivial action. -/
theorem eq_one_of_surjective_of_sub_one_sq_eq_zero (f : Module.End k V)
    (a : Module.End k k) (q : V →ₗ[k] k) (hq : Function.Surjective q)
    (heq : ∀ x, q (f x) = a (q x)) (hf : (f - 1) ^ 2 = 0) : a = 1 := by
  apply eq_one_of_sub_one_sq_eq_zero
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := hq x
  have h := congrArg q (LinearMap.congr_fun hf v)
  simpa only [pow_two, Module.End.mul_apply, LinearMap.sub_apply,
    Module.End.one_apply, map_sub, heq, map_zero, LinearMap.zero_apply] using h

end Module.End

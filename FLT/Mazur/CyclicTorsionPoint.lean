/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Cyclic torsion embeddings and points of exact order

This gives a point-based formulation of the narrow rational torsion input.
It works for any order, including zero for infinite order, without primality
or elliptic-curve hypotheses.
-/

@[expose] public section

namespace FLT.Mazur

/-- A point of order n supplies an injective homomorphism from Z/n. -/
theorem cyclic_embedding_of_addOrderOf {A : Type*} [AddCommGroup A]
    (P : A) (n : ℕ) (hP : addOrderOf P = n) :
    ∃ f : ZMod n →+ A, Function.Injective f := by
  let g : ℤ →+ A :=
    { toFun := fun m ↦ m • P
      map_zero' := zero_zsmul P
      map_add' := fun m k ↦ add_zsmul P m k }
  have hker : g (n : ℤ) = 0 := by
    change (n : ℤ) • P = 0
    rw [natCast_zsmul, ← hP]
    exact addOrderOf_nsmul_eq_zero P
  refine ⟨ZMod.lift n ⟨g, hker⟩, ?_⟩
  rw [ZMod.lift_injective]
  intro m hm
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hd : (addOrderOf P : ℤ) ∣ m :=
    (addOrderOf_dvd_iff_zsmul_eq_zero).2 hm
  simpa only [hP] using hd

/-- A cyclic subgroup embedding is equivalent to a point of exact order n. -/
theorem cyclic_embedding_iff_point {A : Type*} [AddCommGroup A]
    (n : ℕ) :
    (∃ f : ZMod n →+ A, Function.Injective f) ↔ ∃ P : A, addOrderOf P = n := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f 1, ?_⟩
    rw [addOrderOf_injective f hf, ZMod.addOrderOf_one]
  · rintro ⟨P, hP⟩
    exact cyclic_embedding_of_addOrderOf P n hP

end FLT.Mazur

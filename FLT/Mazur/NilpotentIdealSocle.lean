/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Detecting a supported ideal by its simultaneous annihilator

If powers of two coordinates annihilate an ideal, every nonzero element
produces a nonzero element killed by both coordinates. This is an actual
element construction, without finite generation or field hypotheses.
-/

@[expose] public section
namespace FLT.Mazur.NilpotentIdealSocle
variable {A : Type*} [CommRing A]

/-- The part of an ideal annihilated by one specified coordinate. -/
def killedBy (J : Ideal A) (x : A) : Ideal A where
  carrier := {z | z ∈ J ∧ x * z = 0}
  zero_mem' := ⟨J.zero_mem, mul_zero x⟩
  add_mem' := fun ha hb ↦ ⟨J.add_mem ha.1 hb.1, by rw [mul_add, ha.2, hb.2, add_zero]⟩
  smul_mem' := by
    intro a z hz
    exact ⟨J.mul_mem_left a hz.1, by
      change x * (a * z) = 0
      rw [mul_left_comm, hz.2, mul_zero]⟩

/-- A nonzero element killed by a power yields a nonzero element killed by the coordinate. -/
theorem exists_killedBy (J : Ideal A) (x : A) (m : ℕ) {z : A}
    (hz : z ∈ J) (hne : z ≠ 0) (hm : x ^ m * z = 0) :
    ∃ w : A, w ∈ killedBy J x ∧ w ≠ 0 := by
  induction m generalizing z with
  | zero => exact False.elim (hne (by simpa only [pow_zero, one_mul] using hm))
  | succ m ih =>
    by_cases hx : x * z = 0
    · exact ⟨z, ⟨hz, hx⟩, hne⟩
    · exact ih (J.mul_mem_left x hz) hx (by
        simpa only [pow_succ, mul_assoc] using hm)

/-- The simultaneous coordinate annihilator inside the given ideal. -/
def socle (J : Ideal A) (x y : A) : Ideal A := killedBy (killedBy J x) y

/-- Two uniform coordinate annihilation bounds construct a nonzero node socle element. -/
theorem exists_socle (J : Ideal A) (x y : A) (m n : ℕ)
    (hx : ∀ z ∈ J, x ^ m * z = 0) (hy : ∀ z ∈ J, y ^ n * z = 0)
    {z : A} (hz : z ∈ J) (hne : z ≠ 0) :
    ∃ w : A, w ∈ socle J x y ∧ w ≠ 0 := by
  obtain ⟨v, hv, hvne⟩ := exists_killedBy J x m hz hne (hx z hz)
  exact exists_killedBy (killedBy J x) y n hv hvne (hy v hv.1)

/-- Under these bounds, vanishing of the node socle detects vanishing of the entire ideal. -/
theorem socle_eq_bot_iff (J : Ideal A) (x y : A) (m n : ℕ)
    (hx : ∀ z ∈ J, x ^ m * z = 0) (hy : ∀ z ∈ J, y ^ n * z = 0) :
    socle J x y = ⊥ ↔ J = ⊥ := by
  constructor
  · intro hs
    apply le_antisymm _ bot_le
    intro z hz
    by_contra hn
    obtain ⟨w, hw, hwne⟩ := exists_socle J x y m n hx hy hz hn
    exact hwne (Ideal.mem_bot.mp (hs ▸ hw))
  · intro hj
    apply le_antisymm _ bot_le
    intro z hz
    exact hj ▸ hz.1.1

end FLT.Mazur.NilpotentIdealSocle

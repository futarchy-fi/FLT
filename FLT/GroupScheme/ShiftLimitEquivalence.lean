/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Logic.Function.Iterate
public import Mathlib.Logic.Equiv.Defs

/-! # Inverse sequences turn an inverse up to a shift into an equivalence -/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable {A B : Type*}

/-- Sequences compatible with a specified endomorphism. -/
def ShiftLimit (f : A → A) := {x : ℕ → A // ∀ n, f (x (n + 1)) = x n}

/-- Shifting n places in a compatible sequence reverses n applications of the endomorphism. -/
theorem ShiftLimit.iterate_apply {f : A → A} (x : ShiftLimit f) (n k : ℕ) :
    f^[k] (x.val (n + k)) = x.val n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ← Nat.add_assoc, x.property, ih]

/-- A commuting map induces a map of inverse sequences. -/
def ShiftLimit.map {f : A → A} {g : B → B} (q : A → B)
    (hq : ∀ a, q (f a) = g (q a)) (x : ShiftLimit f) : ShiftLimit g :=
  ⟨fun n ↦ q (x.val n), fun n ↦ by rw [← hq, x.property]⟩

/-- A map with an inverse up to a finite shift is invertible on all compatible sequences. -/
def ShiftLimit.equiv {f : A → A} {g : B → B} (q : A → B)
    (hq : ∀ a, q (f a) = g (q a)) (L : B → A) (s : ℕ)
    (hL : ∀ b, L (g b) = f (L b))
    (hLq : ∀ a, L (q a) = f^[s] a) (hqL : ∀ b, q (L b) = g^[s] b) :
    ShiftLimit f ≃ ShiftLimit g where
  toFun := ShiftLimit.map q hq
  invFun x := ⟨fun n ↦ L (x.val (n + s)), fun n ↦ by
    change f (L (x.val (n + 1 + s))) = L (x.val (n + s))
    rw [show n + 1 + s = n + s + 1 by omega, ← hL, x.property]⟩
  left_inv x := by
    apply Subtype.ext
    funext n
    exact (hLq _).trans (x.iterate_apply n s)
  right_inv x := by
    apply Subtype.ext
    funext n
    exact (hqL _).trans (x.iterate_apply n s)

/-- The inverse is the shifted lift, with no compatibility assumptions hidden in a record. -/
theorem ShiftLimit.equiv_symm_apply {f : A → A} {g : B → B} (q : A → B)
    (hq : ∀ a, q (f a) = g (q a)) (L : B → A) (s : ℕ)
    (hL : ∀ b, L (g b) = f (L b))
    (hLq : ∀ a, L (q a) = f^[s] a) (hqL : ∀ b, q (L b) = g^[s] b)
    (x : ShiftLimit g) (n : ℕ) :
    ((ShiftLimit.equiv q hq L s hL hLq hqL).symm x).val n = L (x.val (n + s)) := rfl

end ThreeAdicPlan

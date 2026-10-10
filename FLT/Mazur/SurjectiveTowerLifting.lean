/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Function.Basic

/-!
# Lifting a specified element in a countable surjective inverse system

Choose successive lifts above its prescribed index, then reduce that tail
to all indices. Compatibility uses the original transition maps.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.SurjectiveTowerLifting

universe u

variable {F : ℕ → Type u} (r : ∀ {a b : ℕ}, a ≤ b → F b → F a)
  (hs : ∀ n, Function.Surjective (r (Nat.le_succ n)))

/-- Successively lift a given element, retaining its specified starting index. -/
def liftTail (n : ℕ) (x : F n) : ∀ k, F (n + k)
  | 0 => x
  | k + 1 => (hs (n + k) (liftTail n x k)).choose

/-- Each chosen lift reduces to the preceding chosen element. -/
lemma liftTail_succ (n : ℕ) (x : F n) (k : ℕ) :
    r (Nat.le_succ (n + k)) (liftTail r hs n x (k + 1)) = liftTail r hs n x k :=
  (hs (n + k) (liftTail r hs n x k)).choose_spec

variable (hid : ∀ a (x : F a), r le_rfl x = x)
  (hcomp : ∀ {a b c} (hab : a ≤ b) (hbc : b ≤ c) (x : F c),
    r hab (r hbc x) = r (Nat.le_trans hab hbc) x)

include hid hcomp in
/-- Every pair of coordinates in the chosen tail respects the original transition. -/
lemma liftTail_compatible (n : ℕ) (x : F n) {a b : ℕ} (hab : a ≤ b) :
    r (Nat.add_le_add_left hab n) (liftTail r hs n x b) = liftTail r hs n x a := by
  induction hab with
  | refl => exact hid _ _
  | @step b hab ih =>
    rw [← hcomp (Nat.add_le_add_left hab n) (Nat.le_succ (n + b)),
      liftTail_succ r hs n x b]
    exact ih

include hs hid hcomp in
/-- Every prescribed coordinate extends to a compatible family on the entire tower. -/
theorem exists_compatible (n : ℕ) (x : F n) :
    ∃ y : ∀ k, F k, (∀ a b (hab : a ≤ b), r hab (y b) = y a) ∧ y n = x := by
  let y : ∀ k, F k := fun k ↦ r (Nat.le_add_left k n) (liftTail r hs n x k)
  have hc : ∀ a b (hab : a ≤ b), r hab (y b) = y a := by
    intro a b hab
    dsimp only [y]
    rw [hcomp]
    rw [← hcomp (Nat.le_add_left a n) (Nat.add_le_add_left hab n)]
    rw [liftTail_compatible r hs hid hcomp n x hab]
  refine ⟨y, hc, ?_⟩
  exact liftTail_compatible r hs hid hcomp n x (Nat.zero_le n)

end FLT.Mazur.SurjectiveTowerLifting

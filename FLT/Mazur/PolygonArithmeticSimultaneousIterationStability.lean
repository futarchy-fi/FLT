/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSimultaneousStepStability
public import FLT.Mazur.PolygonArithmeticSimultaneousIteration

/-!
# Stabilization after any finite number of simultaneous corrections

Once the correction order reaches m, all subsequent rounds preserve every
actual smoothing and both complete edge maps on arithmetic quotient m.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticSimultaneous
open PolygonArithmeticStages
variable {R : Type*} [CommRing R] {π : R}
  (B : (m : ℕ) → (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])
  (hB : CompatibleEquiv B) (hb : ReciprocalBase B)
  (S : State R π) (hS : S.Compatible) (ha : S.Annihilated)
  (r₀ : ℕ) (hr₀ : S.Normalized B r₀)
local notation "I" => S.iterate B hB hb hS ha r₀ hr₀

/-- The initial smoothing stabilizes after its arithmetic order is reached. -/
theorem State.iterate_initial_stable {k l m : ℕ} (hkl : k ≤ l) (hm : m ≤ r₀ + k) (b : Bool) :
    (I l).initial m b = (I k).initial m b := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    rw [State.iterate_succ, State.step_initial_stable _ _ _ m (by omega)]
    exact ih

/-- The shared last smoothing stabilizes after its arithmetic order is reached. -/
theorem State.iterate_last_stable {k l m : ℕ} (hkl : k ≤ l) (hm : m ≤ r₀ + k) (b : Bool) :
    (I l).last m b = (I k).last m b := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    rw [State.iterate_succ, State.step_last_stable _ _ _ m (by omega)]
    exact ih

/-- The common terminal smoothing stabilizes after its arithmetic order is reached. -/
theorem State.iterate_terminal_stable {k l m : ℕ} (hkl : k ≤ l) (hm : m ≤ r₀ + k) :
    (I l).terminal m = (I k).terminal m := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    rw [State.iterate_succ, State.step_terminal_stable _ _ _ m (by omega)]
    exact ih

/-- The complete initial edge stabilizes after its arithmetic order is reached. -/
theorem State.iterate_initialEquiv_stable {k l m : ℕ} (hkl : k ≤ l) (hm : m ≤ r₀ + k) (b : Bool) :
    (I l).initialEquiv m b = (I k).initialEquiv m b := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    rw [State.iterate_succ, State.step_initialEquiv_stable _ _ _ m (by omega)]
    exact ih

/-- The complete closing edge stabilizes after its arithmetic order is reached. -/
theorem State.iterate_closingEquiv_stable {k l m : ℕ} (hkl : k ≤ l) (hm : m ≤ r₀ + k) (b : Bool) :
    (I l).closingEquiv m b = (I k).closingEquiv m b := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    rw [State.iterate_succ, State.step_closingEquiv_stable _ _ _ m (by omega)]
    exact ih

end FLT.Mazur.PolygonArithmeticSimultaneous

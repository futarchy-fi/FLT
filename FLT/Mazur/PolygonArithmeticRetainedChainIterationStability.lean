/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainStepStability
public import FLT.Mazur.PolygonArithmeticRetainedChainIteration

/-!
# Stabilization after any finite number of full-chain corrections

Once the correction order reaches m, all subsequent rounds preserve every
actual smoothing and every complete edge map on arithmetic quotient m.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticRetainedChain
open PolygonArithmeticStages PolygonArithmeticSimultaneous
variable {R : Type*} [CommRing R] {π : R} {n : ℕ}
  (B : (m : ℕ) → (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])
  (hB : CompatibleEquiv B) (hb : ReciprocalBase B)
  (S : State R π n) (hS : S.Compatible) (ha : S.Annihilated)
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

/-- The retained smoothing stabilizes after its arithmetic order is reached. -/
theorem State.iterate_retained_stable {k l m : ℕ} (hkl : k ≤ l) (hm : m ≤ r₀ + k)
    (i : Fin (n + 1)) (b : Bool) :
    (I l).retained m i b = (I k).retained m i b := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    rw [State.iterate_succ, State.step_retained_stable _ _ _ m (by omega)]
    exact ih

/-- The common terminal smoothing stabilizes after its arithmetic order is reached. -/
theorem State.iterate_terminal_stable {k l m : ℕ} (hkl : k ≤ l) (hm : m ≤ r₀ + k) :
    (I l).terminal m = (I k).terminal m := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    rw [State.iterate_succ, State.step_terminal_stable _ _ _ m (by omega)]
    exact ih

/-- Every complete edge stabilizes after its arithmetic order is reached. -/
theorem State.iterate_edgeEquiv_stable {k l m : ℕ} (hkl : k ≤ l) (hm : m ≤ r₀ + k)
    (e : Edge n) (b : Bool) :
    (I l).edgeEquiv e m b = (I k).edgeEquiv e m b := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    rw [State.iterate_succ, State.step_edgeEquiv_stable _ _ _ m (by omega)]
    exact ih

end FLT.Mazur.PolygonArithmeticRetainedChain

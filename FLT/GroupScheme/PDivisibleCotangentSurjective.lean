/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCotangentLimit

/-! # Every original level cotangent lifts to the actual inverse limit -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Each original cotangent projection is surjective, by successive actual integral lifts. -/
theorem cotangentEval_surjective (n : ℕ) : Function.Surjective (X.cotangentEval n) := by
  intro a
  let s : ∀ k : ℕ, X.LevelCotangent (n + k) := fun k ↦ Nat.rec a
    (fun j b ↦ (X.cotangentRestriction_surjective (Nat.le_succ (n + j)) b).choose) k
  have hs (k : ℕ) : X.cotangentRestriction (Nat.le_succ (n + k)) (s (k + 1)) = s k :=
    (X.cotangentRestriction_surjective (Nat.le_succ (n + k)) (s k)).choose_spec
  have hall {i j : ℕ} (h : i ≤ j) :
      X.cotangentRestriction (Nat.add_le_add_left h n) (s j) = s i := by
    induction j, h using Nat.le_induction with
    | base => rw [X.cotangentRestriction_refl]; rfl
    | succ j h ih =>
      have he := X.cotangentRestriction_comp (Nat.add_le_add_left h n) (Nat.le_succ (n + j))
      rw [← he]
      change X.cotangentRestriction _ (X.cotangentRestriction _ (s (j + 1))) = _
      rw [hs, ih]
  let x (m : ℕ) : X.LevelCotangent m :=
    X.cotangentRestriction (Nat.le_add_left m n) (s m)
  have hx {m k : ℕ} (h : m ≤ k) : X.cotangentRestriction h (x k) = x m := by
    have he := hall h
    dsimp [x]
    change ((X.cotangentRestriction h).comp
      (X.cotangentRestriction (Nat.le_add_left k n))) (s k) = _
    rw [X.cotangentRestriction_comp, ← he]
    change _ = ((X.cotangentRestriction (Nat.le_add_left m n)).comp
      (X.cotangentRestriction (Nat.add_le_add_left h n))) (s k)
    rw [X.cotangentRestriction_comp]
  refine ⟨⟨x, fun h ↦ hx h⟩, ?_⟩
  exact hall (Nat.zero_le n)

end ThreeAdicPlan.PDivisibleSystem

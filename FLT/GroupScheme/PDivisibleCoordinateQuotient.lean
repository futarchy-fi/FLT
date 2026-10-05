/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCoordinateLimit
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Original finite levels as quotients of the coordinate inverse limit -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Closedness of the original inclusions gives surjectivity of every limit evaluation. -/
theorem coordinateEval_surjective (n : ℕ) : Function.Surjective (X.coordinateEval n) := by
  intro a
  let s : ∀ k : ℕ, (X.level (n + k)).CoordinateRing := fun k ↦ Nat.rec a
    (fun j b ↦ (X.closed (Nat.le_succ (n + j)) b).choose) k
  have hs (k : ℕ) : X.inclusion (Nat.le_succ (n + k)) (s (k + 1)) = s k :=
    (X.closed (Nat.le_succ (n + k)) (s k)).choose_spec
  have hall {i j : ℕ} (h : i ≤ j) :
      X.inclusion (Nat.add_le_add_left h n) (s j) = s i := by
    induction j, h using Nat.le_induction with
    | base => rw [X.inclusion_refl]; rfl
    | succ j h ih =>
      rw [← X.inclusion_comp (Nat.add_le_add_left h n) (Nat.le_succ (n + j))]
      change X.inclusion _ (X.inclusion _ (s (j + 1))) = _
      rw [hs, ih]
  let x (m : ℕ) : (X.level m).CoordinateRing := X.inclusion (Nat.le_add_left m n) (s m)
  have hx {m k : ℕ} (h : m ≤ k) : X.inclusion h (x k) = x m := by
    have he := hall h
    dsimp [x]
    change ((X.inclusion h).comp (X.inclusion (Nat.le_add_left k n))) (s k) = _
    rw [X.inclusion_comp, ← he]
    change _ = ((X.inclusion (Nat.le_add_left m n)).comp
      (X.inclusion (Nat.add_le_add_left h n))) (s k)
    rw [X.inclusion_comp]
  exact ⟨⟨x, fun h ↦ hx h⟩, hall (Nat.zero_le n)⟩

/-- The level ideals of the original coordinate limit. -/
def coordinateIdeal (n : ℕ) : Ideal X.coordinateLimit := RingHom.ker (X.coordinateEval n)

/-- The original coordinate algebra is the quotient by its evaluation kernel. -/
def coordinateQuotientEquiv (n : ℕ) :
    (X.coordinateLimit ⧸ X.coordinateIdeal n) ≃ₐ[R] (X.level n).CoordinateRing :=
  Ideal.quotientKerAlgEquivOfSurjective (X.coordinateEval_surjective n)

/-- The quotient identification uses the original evaluation. -/
theorem coordinateQuotientEquiv_mk (n : ℕ) (x : X.coordinateLimit) :
    X.coordinateQuotientEquiv n (Ideal.Quotient.mk _ x) = X.coordinateEval n x := rfl

/-- Higher original levels give smaller ideals of definition. -/
theorem coordinateIdeal_antitone : Antitone X.coordinateIdeal := by
  intro m n h x hx
  change X.coordinateEval m x = 0
  rw [← X.coordinateEval_inclusion h x]
  change X.coordinateEval n x = 0 at hx
  rw [hx, map_zero]

/-- The level-ideal filtration is separated. -/
theorem coordinateIdeal_iInf : ⨅ n, X.coordinateIdeal n = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  apply X.coordinateLimit_ext
  intro n
  exact (Ideal.mem_iInf.mp hx n : X.coordinateEval n x = 0)

end ThreeAdicPlan.PDivisibleSystem

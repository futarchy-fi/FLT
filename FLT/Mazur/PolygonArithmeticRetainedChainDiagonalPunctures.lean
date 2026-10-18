/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainPunctureStability
public import FLT.Mazur.PolygonArithmeticRetainedChainPunctureRestriction

/-!
# Diagonal coefficient squares for the complete finite punctures

The correction count changes from m to m+1 across the adjacent quotient.
Stabilization of the additional full factor gives the exact original square.
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

/-- Both diagonal initial punctures have their full arithmetic coefficient square. -/
theorem State.diagonalInitialPuncture_compatible (b c : Bool) :
    CompatibleEquiv (fun m ↦ S.iterateInitialPuncture B hB hb hS ha r₀ hr₀ m b c m) := by
  intro m
  have h := S.iterateInitialPuncture_compatible B hB hb hS ha r₀ hr₀ b c (m + 1) m
  dsimp only at h
  rw [S.iterateInitialPuncture_stable B hB hb hS ha r₀ hr₀ m
    (Nat.le_succ m) (by omega) b c] at h
  exact h

/-- Both diagonal retained punctures have their full arithmetic coefficient square. -/
theorem State.diagonalRetainedPuncture_compatible (i : Fin (n + 1)) (b c : Bool) :
    CompatibleEquiv (fun m ↦ S.iterateRetainedPuncture B hB hb hS ha r₀ hr₀ m i b c m) := by
  intro m
  have h := S.iterateRetainedPuncture_compatible B hB hb hS ha r₀ hr₀ i b c (m + 1) m
  dsimp only at h
  rw [S.iterateRetainedPuncture_stable B hB hb hS ha r₀ hr₀ m
    (Nat.le_succ m) (by omega) i b c] at h
  exact h

/-- Both diagonal terminal punctures have their full arithmetic coefficient square. -/
theorem State.diagonalTerminalPuncture_compatible (b : Bool) :
    CompatibleEquiv (fun m ↦ S.iterateTerminalPuncture B hB hb hS ha r₀ hr₀ m b m) := by
  intro m
  have h := S.iterateTerminalPuncture_compatible B hB hb hS ha r₀ hr₀ b (m + 1) m
  dsimp only at h
  rw [S.iterateTerminalPuncture_stable B hB hb hS ha r₀ hr₀ m
    (Nat.le_succ m) (by omega) b] at h
  exact h

end FLT.Mazur.PolygonArithmeticRetainedChain

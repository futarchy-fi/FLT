/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainFields

/-!
# Embed the constructed depth-zero states in the retained-chain representation

The one retained node supplies both boundary edges. There are no internal
incoming edges at depth zero, so no predecessor packet or hypothesis is used.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticRetainedChain
open PolygonArithmeticStages PolygonArithmeticSimultaneous
variable {R : Type*} [CommRing R] {π : R}
  (S : PolygonArithmeticSimultaneous.State R π)

/-- The same initial, last, terminal and complete boundary overlaps form a depth-zero chain. -/
def ofDepthZero : State R π 0 where
  initial := S.initial
  retained m _ := S.last m
  terminal := S.terminal
  edgeEquiv
    | .initial => S.initialEquiv
    | .incoming i => Fin.elim0 i
    | .closing => S.closingEquiv

/-- The actual depth-zero coefficient squares supply all retained-chain squares. -/
theorem ofDepthZero_compatible (hS : S.Compatible) : (ofDepthZero S).Compatible := by
  refine ⟨hS.1, (fun m _ b ↦ hS.2.1 m b), hS.2.2.1, ?_⟩
  intro e b
  cases e with
  | initial => exact hS.2.2.2.1 b
  | incoming i => exact Fin.elim0 i
  | closing => exact hS.2.2.2.2 b

/-- Every actual depth-zero annihilator survives the full retained-chain representation. -/
theorem ofDepthZero_annihilated (ha : S.Annihilated) : (ofDepthZero S).Annihilated :=
  ⟨ha.1, (fun m _ b ↦ ha.2.1 m b), ha.2.2⟩

variable (B : (m : ℕ) →
  (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])

/-- Normalizing the chain at depth zero is exactly normalizing its two actual boundary edges. -/
theorem ofDepthZero_normalized_iff (r : ℕ) :
    (ofDepthZero S).Normalized B r ↔ S.Normalized B r := by
  constructor
  · intro h
    exact ⟨h .initial, h .closing⟩
  · intro h e b
    cases e with
    | initial => exact h.1 b
    | incoming i => exact Fin.elim0 i
    | closing => exact h.2 b

end FLT.Mazur.PolygonArithmeticRetainedChain

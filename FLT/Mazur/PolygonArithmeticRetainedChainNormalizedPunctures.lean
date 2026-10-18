/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainFiniteResiduals

/-!
# Complete finite puncture comparisons normalize every attained edge

The original seed overlap remains explicit between the actual accumulated
punctures. These are full Laurent equalities for installing corrected atlases.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticRetainedChain
open PolygonArithmeticStages PolygonArithmeticSimultaneous
variable {R : Type*} [CommRing R] {π : R} {n : ℕ}
  (B : (m : ℕ) → (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])
  (hB : CompatibleEquiv B) (hb : ReciprocalBase B)
  (S : State R π n) (hS : S.Compatible) (ha : S.Annihilated)
  (r₀ : ℕ) (hr₀ : S.Normalized B r₀) (k m : ℕ) (hm : m ≤ r₀ + k)
local notation "a" => S.iterateInitialPuncture B hB hb hS ha r₀ hr₀ m
local notation "v" => S.iterateRetainedPuncture B hB hb hS ha r₀ hr₀ m
local notation "t" => S.iterateTerminalPuncture B hB hb hS ha r₀ hr₀ m
local notation "o" => S.iterateOutgoingFactor B hB hb hS ha r₀ hr₀ m

include hm

/-- The full initial seed overlap retains exactly its original reciprocal base. -/
theorem State.finite_initial_normalized (b : Bool) :
    ((v 0 b false k).trans (S.edgeEquiv .initial m b)).trans (a b true k).symm = B m := by
  rw [← State.iterate_initialEquiv]
  exact S.iterate_normalized_le B hB hb hS ha r₀ hr₀ k m hm .initial b

/-- Each original internal seed edge is canceled by its two actual adjacent finite factors. -/
theorem State.finite_incoming_normalized (i : Fin n) (b : Bool) :
    ((v i.succ b false k).trans (S.edgeEquiv (.incoming i) m b)).trans
      (o i.castSucc b k).symm = AlgEquiv.refl := by
  rw [← State.iterate_incomingEquiv]
  exact S.iterate_normalized_le B hB hb hS ha r₀ hr₀ k m hm (.incoming i) b

/-- Both original closing edges are canceled by the last node and common terminal factors. -/
theorem State.finite_closing_normalized (b : Bool) :
    ((t b k).symm.trans (S.edgeEquiv .closing m b)).trans
      (o (Fin.last n) b k).symm = AlgEquiv.refl := by
  rw [← State.iterate_closingEquiv]
  exact S.iterate_normalized_le B hB hb hS ha r₀ hr₀ k m hm .closing b

end FLT.Mazur.PolygonArithmeticRetainedChain

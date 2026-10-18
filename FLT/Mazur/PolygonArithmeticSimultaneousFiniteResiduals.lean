/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSimultaneousFinitePunctures

/-!
# Full finite residuals as conjugates by the actual composite punctures

These identities retain the entire seed overlaps, including every initial
base parameter and both punctures of the same last-node comparison.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticSimultaneous
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R}
  (B : (m : ℕ) → (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])
  (hB : CompatibleEquiv B) (hb : ReciprocalBase B)
  (S : State R π) (hS : S.Compatible) (ha : S.Annihilated)
  (r₀ : ℕ) (hr₀ : S.Normalized B r₀)
local notation "P" => S.iterateAux B hB hb hS ha r₀ hr₀
variable (m : ℕ)
local notation "a" => S.iterateInitialPuncture B hB hb hS ha r₀ hr₀ m
local notation "l" => S.iterateLastPuncture B hB hb hS ha r₀ hr₀ m
local notation "t" => S.iterateTerminalPuncture B hB hb hS ha r₀ hr₀ m

/-- The finite outgoing last comparison in the closing-edge coordinate. -/
def State.iterateLastEdge (b : Bool) (k : ℕ) :
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  (invert.trans (l b true k)).trans invert

/-- The complete auxiliary initial overlap is conjugated by the finite node punctures. -/
theorem State.iterateAux_initialEquiv (b : Bool) (k : ℕ) :
    (P k).val.initialEquiv m b =
      ((l b false k).trans (S.initialEquiv m b)).trans (a b true k).symm := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (AlgEquiv.trans (AlgEquiv.trans _ ((P k).val.initialEquiv m b)) _) = _
    rw [ih]
    ext x
    rfl

/-- The complete auxiliary closing overlap keeps the common terminal and shared last factor. -/
theorem State.iterateAux_closingEquiv (b : Bool) (k : ℕ) :
    (P k).val.closingEquiv m b =
      ((t b k).symm.trans (S.closingEquiv m b)).trans
        (S.iterateLastEdge B hB hb hS ha r₀ hr₀ m b k).symm := by
  induction k with
  | zero =>
    apply AlgEquiv.ext
    intro x
    change (S.closingEquiv m b) x = invert (invert ((S.closingEquiv m b) x))
    exact (involutive_invert _).symm
  | succ k ih =>
    change (AlgEquiv.trans (AlgEquiv.trans _ ((P k).val.closingEquiv m b)) _) = _
    rw [ih]
    have hinv (x : (Quotient R π m)[T;T⁻¹]) : invert (invert x) = x :=
      involutive_invert x
    ext x
    simp only [State.iterateLastEdge, State.iterateTerminalPuncture,
      State.iterateLastPuncture, State.lastEdge, AlgEquiv.trans_apply,
      AlgEquiv.symm_trans_apply, invert_symm, hinv, State.iterateSelectedFieldAux]

attribute [local irreducible] State.iterateAux State.iterateInitialPuncture
  State.iterateLastPuncture State.iterateTerminalPuncture
local notation "I" => S.iterate B hB hb hS ha r₀ hr₀

/-- The sealed finite initial overlap uses the complete finite puncture comparisons. -/
theorem State.iterate_initialEquiv (b : Bool) (k : ℕ) :
    (I k).initialEquiv m b =
      ((l b false k).trans (S.initialEquiv m b)).trans (a b true k).symm := by
  rw [State.iterate_def]
  exact S.iterateAux_initialEquiv B hB hb hS ha r₀ hr₀ m b k

/-- The sealed finite closing overlap uses the same finite last and common terminal factors. -/
theorem State.iterate_closingEquiv (b : Bool) (k : ℕ) :
    (I k).closingEquiv m b =
      ((t b k).symm.trans (S.closingEquiv m b)).trans
        (S.iterateLastEdge B hB hb hS ha r₀ hr₀ m b k).symm := by
  rw [State.iterate_def]
  exact S.iterateAux_closingEquiv B hB hb hS ha r₀ hr₀ m b k

end FLT.Mazur.PolygonArithmeticSimultaneous

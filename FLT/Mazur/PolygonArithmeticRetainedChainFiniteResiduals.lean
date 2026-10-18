/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainFinitePunctures

/-!
# Full finite residuals as conjugates by the actual composite punctures

These identities retain the entire seed overlaps, including every initial
base parameter and both punctures of the same retained-node comparison.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticRetainedChain
open PolygonArithmeticStages PolygonArithmeticSimultaneous PolygonSmoothing LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R} {n : ℕ}
  (B : (m : ℕ) → (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])
  (hB : CompatibleEquiv B) (hb : ReciprocalBase B)
  (S : State R π n) (hS : S.Compatible) (ha : S.Annihilated)
  (r₀ : ℕ) (hr₀ : S.Normalized B r₀)
local notation "P" => S.iterateAux B hB hb hS ha r₀ hr₀
variable (m : ℕ)
local notation "a" => S.iterateInitialPuncture B hB hb hS ha r₀ hr₀ m
local notation "l" => S.iterateRetainedPuncture B hB hb hS ha r₀ hr₀ m
local notation "t" => S.iterateTerminalPuncture B hB hb hS ha r₀ hr₀ m

/-- The finite outgoing retained comparison in its edge coordinate. -/
def State.iterateOutgoingFactor (i : Fin (n + 1)) (b : Bool) (k : ℕ) :
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  (invert.trans (l i b true k)).trans invert

/-- The complete auxiliary initial overlap is conjugated by the finite node punctures. -/
theorem State.iterateAux_initialEquiv (b : Bool) (k : ℕ) :
    (P k).val.edgeEquiv .initial m b =
      ((l 0 b false k).trans (S.edgeEquiv .initial m b)).trans (a b true k).symm := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (AlgEquiv.trans (AlgEquiv.trans _ ((P k).val.edgeEquiv .initial m b)) _) = _
    rw [ih]
    ext x
    rfl

/-- The complete auxiliary closing overlap keeps the common terminal and shared last factor. -/
theorem State.iterateAux_closingEquiv (b : Bool) (k : ℕ) :
    (P k).val.edgeEquiv .closing m b =
      ((t b k).symm.trans (S.edgeEquiv .closing m b)).trans
        (S.iterateOutgoingFactor B hB hb hS ha r₀ hr₀ m (Fin.last n) b k).symm := by
  induction k with
  | zero =>
    apply AlgEquiv.ext
    intro x
    change (S.edgeEquiv .closing m b) x = invert (invert ((S.edgeEquiv .closing m b) x))
    exact (involutive_invert _).symm
  | succ k ih =>
    change (AlgEquiv.trans (AlgEquiv.trans _ ((P k).val.edgeEquiv .closing m b)) _) = _
    rw [ih]
    have hinv (x : (Quotient R π m)[T;T⁻¹]) : invert (invert x) = x :=
      involutive_invert x
    ext x
    simp only [State.iterateOutgoingFactor, State.iterateTerminalPuncture,
      State.iterateRetainedPuncture, State.outgoingFactor, AlgEquiv.trans_apply,
      AlgEquiv.symm_trans_apply, invert_symm, hinv, State.iterateSelectedFieldAux]

/-- Each full internal overlap uses the two adjacent finite retained comparisons. -/
theorem State.iterateAux_incomingEquiv (i : Fin n) (b : Bool) (k : ℕ) :
    (P k).val.edgeEquiv (.incoming i) m b =
      ((l i.succ b false k).trans (S.edgeEquiv (.incoming i) m b)).trans
        (S.iterateOutgoingFactor B hB hb hS ha r₀ hr₀ m i.castSucc b k).symm := by
  induction k with
  | zero =>
    apply AlgEquiv.ext
    intro x
    change (S.edgeEquiv (.incoming i) m b) x =
      invert (invert ((S.edgeEquiv (.incoming i) m b) x))
    exact (involutive_invert _).symm
  | succ k ih =>
    change (AlgEquiv.trans (AlgEquiv.trans _ ((P k).val.edgeEquiv (.incoming i) m b)) _) = _
    rw [ih]
    have hinv (x : (Quotient R π m)[T;T⁻¹]) : invert (invert x) = x :=
      involutive_invert x
    ext x
    simp only [State.iterateOutgoingFactor, State.iterateRetainedPuncture,
      State.outgoingFactor, AlgEquiv.trans_apply, AlgEquiv.symm_trans_apply,
      invert_symm, hinv, State.iterateSelectedFieldAux]

attribute [local irreducible] State.iterateAux State.iterateInitialPuncture
  State.iterateRetainedPuncture State.iterateTerminalPuncture
local notation "I" => S.iterate B hB hb hS ha r₀ hr₀

/-- The sealed finite initial overlap uses the complete finite puncture comparisons. -/
theorem State.iterate_initialEquiv (b : Bool) (k : ℕ) :
    (I k).edgeEquiv .initial m b =
      ((l 0 b false k).trans (S.edgeEquiv .initial m b)).trans (a b true k).symm := by
  rw [State.iterate_def]
  exact S.iterateAux_initialEquiv B hB hb hS ha r₀ hr₀ m b k

/-- The sealed finite closing overlap uses the same finite last and common terminal factors. -/
theorem State.iterate_closingEquiv (b : Bool) (k : ℕ) :
    (I k).edgeEquiv .closing m b =
      ((t b k).symm.trans (S.edgeEquiv .closing m b)).trans
        (S.iterateOutgoingFactor B hB hb hS ha r₀ hr₀ m (Fin.last n) b k).symm := by
  rw [State.iterate_def]
  exact S.iterateAux_closingEquiv B hB hb hS ha r₀ hr₀ m b k

/-- The sealed finite internal edge retains both adjacent whole-node comparisons. -/
theorem State.iterate_incomingEquiv (i : Fin n) (b : Bool) (k : ℕ) :
    (I k).edgeEquiv (.incoming i) m b =
      ((l i.succ b false k).trans (S.edgeEquiv (.incoming i) m b)).trans
        (S.iterateOutgoingFactor B hB hb hS ha r₀ hr₀ m i.castSucc b k).symm := by
  rw [State.iterate_def]
  exact S.iterateAux_incomingEquiv B hB hb hS ha r₀ hr₀ m i b k

end FLT.Mazur.PolygonArithmeticRetainedChain

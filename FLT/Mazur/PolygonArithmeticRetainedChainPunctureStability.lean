/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainPunctureIteration
public import FLT.Mazur.PolygonArithmeticHigherPairedStability

/-!
# Finite full puncture comparisons stabilize on earlier quotients

Every late added factor is identity on both branches. The complete accumulated
initial, shared retained, and rebased terminal substitutions therefore stabilize.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticRetainedChain
open PolygonArithmeticStages PolygonArithmeticSimultaneous
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] State.iterateAux
variable {R : Type*} [CommRing R] {π : R} {n : ℕ}
  (B : (m : ℕ) → (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])
  (hB : CompatibleEquiv B) (hb : ReciprocalBase B)
  (S : State R π n) (hS : S.Compatible) (ha : S.Annihilated)
  (r₀ : ℕ) (hr₀ : S.Normalized B r₀) (m : ℕ)

/-- Both full finite initial substitutions stabilize after reaching this quotient. -/
theorem State.iterateInitialPuncture_stable {k l : ℕ} (hkl : k ≤ l)
    (hm : m ≤ r₀ + k) (b c : Bool) :
    S.iterateInitialPuncture B hB hb hS ha r₀ hr₀ m b c l =
      S.iterateInitialPuncture B hB hb hS ha r₀ hr₀ m b c k := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    rw [State.iterateInitialPuncture]
    unfold initialInput
    rw [correctionPunctureFactor_higher_stable R π m (r₀ + l) (by omega)]
    exact ih

/-- Both full finite retained substitutions stabilize after reaching this quotient. -/
theorem State.iterateRetainedPuncture_stable {k l : ℕ} (hkl : k ≤ l)
    (hm : m ≤ r₀ + k) (i : Fin (n + 1)) (b c : Bool) :
    S.iterateRetainedPuncture B hB hb hS ha r₀ hr₀ m i b c l =
      S.iterateRetainedPuncture B hB hb hS ha r₀ hr₀ m i b c k := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    rw [State.iterateRetainedPuncture]
    unfold retainedInput
    rw [twoBranchCorrectionPunctureFactor_higher_stable R π m (r₀ + l) (by omega)]
    exact ih

/-- Both full finite terminal substitutions stabilize after reaching this quotient. -/
theorem State.iterateTerminalPuncture_stable {k l : ℕ} (hkl : k ≤ l)
    (hm : m ≤ r₀ + k) (b : Bool) :
    S.iterateTerminalPuncture B hB hb hS ha r₀ hr₀ m b l =
      S.iterateTerminalPuncture B hB hb hS ha r₀ hr₀ m b k := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    rw [State.iterateTerminalPuncture]
    unfold terminalInput
    rw [twoBranchCorrectionRebasedPunctureFactor_higher_stable R π m (r₀ + l) (by omega)]
    exact ih

end FLT.Mazur.PolygonArithmeticRetainedChain

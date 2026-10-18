/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainFactors

/-!
# Both punctures of the finite retained-chain whole-node comparisons

The same recursively selected fields define the full node factors and their
complete Laurent substitutions. The terminal composite retains its rebasing
orientation, while the initial and retained composites point back to their seeds.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticRetainedChain
open PolygonArithmeticStages PolygonArithmeticSimultaneous PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R} {n : ℕ}
  (B : (m : ℕ) → (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])
  (hB : CompatibleEquiv B) (hb : ReciprocalBase B)
  (S : State R π n) (hS : S.Compatible) (ha : S.Annihilated)
  (r₀ : ℕ) (hr₀ : S.Normalized B r₀)
local notation "P" => S.iterateAux B hB hb hS ha r₀ hr₀
local notation "F" => S.iterateSelectedFieldAux B hB hb hS ha r₀ hr₀
variable (m : ℕ)
local notation "Q" => Quotient R π m

/-- The full initial puncture substitution along the selected finite corrections. -/
def State.iterateInitialPuncture (b c : Bool) : ℕ → Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹]
  | 0 => AlgEquiv.refl
  | k + 1 => (correctionPunctureFactor R π m ((P k).val.initial m b)
      (initialInput (π := π) (r₀ + k) (F k) b) c).trans
        (State.iterateInitialPuncture b c k)

/-- Both retained punctures come from the same finite sequence of two-branch node factors. -/
def State.iterateRetainedPuncture (i : Fin (n + 1)) (b c : Bool) : ℕ → Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹]
  | 0 => AlgEquiv.refl
  | k + 1 => (twoBranchCorrectionPunctureFactor R π m ((P k).val.retained m i b)
      (retainedInput (π := π) (r₀ + k) (F k) i b) c).trans
        (State.iterateRetainedPuncture i b c k)

/-- Both common terminal substitutions retain the complete finite rebasing sequence. -/
def State.iterateTerminalPuncture (b : Bool) : ℕ → Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹]
  | 0 => AlgEquiv.refl
  | k + 1 => (State.iterateTerminalPuncture b k).trans
      (twoBranchCorrectionRebasedPunctureFactor R π m ((P k).val.terminal m)
        (terminalInput (π := π) (r₀ + k) (F k)) b)

local notation "A" => S.iterateInitialFactorAux B hB hb hS ha r₀ hr₀ m
local notation "L" => S.iterateRetainedFactorAux B hB hb hS ha r₀ hr₀ m
local notation "T" => S.iterateTerminalFactorAux B hB hb hS ha r₀ hr₀ m
local notation "a" => S.iterateInitialPuncture B hB hb hS ha r₀ hr₀ m
local notation "l" => S.iterateRetainedPuncture B hB hb hS ha r₀ hr₀ m
local notation "t" => S.iterateTerminalPuncture B hB hb hS ha r₀ hr₀ m

/-- Both initial Laurent maps are induced by the full finite initial node comparison. -/
theorem State.iterateInitialFactorAux_puncture (b c : Bool) (k : ℕ) :
    (punctureLaurentMap (S.initial m b) c).comp (A b k).toAlgHom =
      (a b c k).toAlgHom.comp (punctureLaurentMap ((P k).val.initial m b) c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (punctureLaurentMap (S.initial m b) c).comp ((A b k).toAlgHom.comp
      ((P k).val.initialFactor (r₀ + k) (F k) m b).toAlgHom) =
      ((a b c k).toAlgHom.comp (correctionPunctureFactor R π m ((P k).val.initial m b)
        (initialInput (π := π) (r₀ + k) (F k) b) c).toAlgHom).comp _
    rw [← AlgHom.comp_assoc, ih, AlgHom.comp_assoc, State.initialFactor_puncture,
      ← AlgHom.comp_assoc]
    rfl

/-- Both retained Laurent maps are induced by the same full finite retained comparison. -/
theorem State.iterateRetainedFactorAux_puncture (i : Fin (n + 1)) (b c : Bool) (k : ℕ) :
    (punctureLaurentMap (S.retained m i b) c).comp (L i b k).toAlgHom =
      (l i b c k).toAlgHom.comp (punctureLaurentMap ((P k).val.retained m i b) c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (punctureLaurentMap (S.retained m i b) c).comp ((L i b k).toAlgHom.comp
      ((P k).val.retainedFactor (r₀ + k) (F k) m i b).toAlgHom) =
      ((l i b c k).toAlgHom.comp (twoBranchCorrectionPunctureFactor R π m ((P k).val.retained m i b)
        (retainedInput (π := π) (r₀ + k) (F k) i b) c).toAlgHom).comp _
    rw [← AlgHom.comp_assoc, ih, AlgHom.comp_assoc, State.retainedFactor_puncture,
      ← AlgHom.comp_assoc]
    rfl

/-- Both terminal Laurent maps are induced by the full common terminal comparison. -/
theorem State.iterateTerminalFactorAux_puncture (b : Bool) (k : ℕ) :
    (punctureLaurentMap ((P k).val.terminal m) b).comp (T k).toAlgHom =
      (t b k).toAlgHom.comp (punctureLaurentMap (S.terminal m) b) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (punctureLaurentMap _ b).comp
      (((P k).val.terminalFactor (r₀ + k) (F k) m).toAlgHom.comp (T k).toAlgHom) =
      ((twoBranchCorrectionRebasedPunctureFactor R π m ((P k).val.terminal m)
        (terminalInput (π := π) (r₀ + k) (F k)) b).toAlgHom.comp (t b k).toAlgHom).comp _
    rw [← AlgHom.comp_assoc, State.terminalFactor_puncture, AlgHom.comp_assoc, ih,
      ← AlgHom.comp_assoc]

end FLT.Mazur.PolygonArithmeticRetainedChain

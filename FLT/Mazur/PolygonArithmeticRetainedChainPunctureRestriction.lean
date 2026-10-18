/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainFinitePunctures

/-!
# Coefficient naturality of every full finite puncture

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

open LaurentUnitSubstitutionNaturality
local notation "F" => S.iterateSelectedFieldAux B hB hb hS ha r₀ hr₀

/-- Expose compatibility without unfolding the recursively constructed proof tuple. -/
theorem State.iterateAux_compatible (k : ℕ) : (P k).val.Compatible :=
  (P k).property.1

local notation "hP" => S.iterateAux_compatible B hB hb hS ha r₀ hr₀
attribute [local irreducible] State.iterateAux

/-- Both finite initial punctures retain their full coefficient squares. -/
theorem State.iterateInitialPuncture_compatible (b c : Bool) (k : ℕ) :
    CompatibleEquiv (fun m ↦ S.iterateInitialPuncture B hB hb hS ha r₀ hr₀ m b c k) := by
  induction k with
  | zero => intro m; rfl
  | succ k ih =>
    intro m
    apply punctureEquiv_trans_naturality
    · exact correctionPunctureFactor_restriction R π m _ _ ((hP k).1 m b)
        (initialInput (π := π) (r₀ + k) (F k) b) c
    · exact ih m

/-- The two punctures of the same finite retained comparison are coefficient compatible. -/
theorem State.iterateRetainedPuncture_compatible (i : Fin (n + 1)) (b c : Bool) (k : ℕ) :
    CompatibleEquiv (fun m ↦ S.iterateRetainedPuncture B hB hb hS ha r₀ hr₀ m i b c k) := by
  induction k with
  | zero => intro m; rfl
  | succ k ih =>
    intro m
    apply punctureEquiv_trans_naturality
    · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
        ((hP k).2.1 m i b) (retainedInput (π := π) (r₀ + k) (F k) i b) c
    · exact ih m

/-- Both finite common terminal substitutions respect the actual coefficient quotients. -/
theorem State.iterateTerminalPuncture_compatible (b : Bool) (k : ℕ) :
    CompatibleEquiv (fun m ↦ S.iterateTerminalPuncture B hB hb hS ha r₀ hr₀ m b k) := by
  induction k with
  | zero => intro m; rfl
  | succ k ih =>
    intro m
    apply punctureEquiv_trans_naturality
    · exact ih m
    · exact twoBranchCorrectionRebasedPunctureFactor_restriction R π m _ _
        ((hP k).2.2.1 m) (terminalInput (π := π) (r₀ + k) (F k)) b

end FLT.Mazur.PolygonArithmeticRetainedChain

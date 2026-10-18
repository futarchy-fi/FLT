/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainDiagonalPunctures
public import FLT.Mazur.PolygonArithmeticRetainedChainDiagonal
public import FLT.Mazur.PolygonSmoothingPunctureSquare

/-!
# Coefficient squares for the actual diagonal whole-node factors

The full diagonal Laurent substitutions are coefficient compatible even when
the correction count changes. Both punctures force the whole-node squares.
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
attribute [local irreducible] State.iterateAux State.iterateInitialFactorAux
  State.iterateRetainedFactorAux State.iterateTerminalFactorAux
local notation "I" => S.iterate B hB hb hS ha r₀ hr₀
local notation "D" => S.diagonal B hB hb hS ha r₀ hr₀
local notation "hD" => S.diagonal_compatible B hB hb hS ha r₀ hr₀
variable (m : ℕ)
local notation "f" => AlgHom.toRingHom (restriction R π m)



/-- The diagonal initial comparison retains its exact coefficient square. -/
theorem State.diagonalInitialFactor_restriction (b : Bool) :
    (ringMap f (S.initial (m + 1) b) (S.initial m b) (hS.1 m b)).comp
      (S.iterateInitialFactor B hB hb hS ha r₀ hr₀ (m + 1) (m + 1) b).toRingHom =
    (S.iterateInitialFactor B hB hb hS ha r₀ hr₀ m m b).toRingHom.comp
      (ringMap f ((D).initial (m + 1) b) ((D).initial m b) ((hD).1 m b)) := by
  apply punctureFactor_coefficientSquare
    (a := fun c ↦ S.iterateInitialPuncture B hB hb hS ha r₀ hr₀ (m + 1) b c (m + 1))
    (d := fun c ↦ S.iterateInitialPuncture B hB hb hS ha r₀ hr₀ m b c m)
  · exact fun c ↦ S.iterateInitialFactor_puncture B hB hb hS ha r₀ hr₀ (m + 1) (m + 1) b c
  · exact fun c ↦ S.iterateInitialFactor_puncture B hB hb hS ha r₀ hr₀ m m b c
  · exact fun c ↦ S.diagonalInitialPuncture_compatible B hB hb hS ha r₀ hr₀ b c m

/-- The diagonal retained comparison retains its exact coefficient square. -/
theorem State.diagonalRetainedFactor_restriction (i : Fin (n + 1)) (b : Bool) :
    (ringMap f (S.retained (m + 1) i b) (S.retained m i b) (hS.2.1 m i b)).comp
      (S.iterateRetainedFactor B hB hb hS ha r₀ hr₀ (m + 1) (m + 1) i b).toRingHom =
    (S.iterateRetainedFactor B hB hb hS ha r₀ hr₀ m m i b).toRingHom.comp
      (ringMap f ((D).retained (m + 1) i b) ((D).retained m i b) ((hD).2.1 m i b)) := by
  apply punctureFactor_coefficientSquare
    (a := fun c ↦ S.iterateRetainedPuncture B hB hb hS ha r₀ hr₀ (m + 1) i b c (m + 1))
    (d := fun c ↦ S.iterateRetainedPuncture B hB hb hS ha r₀ hr₀ m i b c m)
  · exact fun c ↦ S.iterateRetainedFactor_puncture B hB hb hS ha r₀ hr₀ (m + 1) (m + 1) i b c
  · exact fun c ↦ S.iterateRetainedFactor_puncture B hB hb hS ha r₀ hr₀ m m i b c
  · exact fun c ↦ S.diagonalRetainedPuncture_compatible B hB hb hS ha r₀ hr₀ i b c m

/-- The sealed common terminal comparison retains the full rebased quotient square. -/
theorem State.diagonalTerminalFactor_restriction :
    (ringMap f ((D).terminal (m + 1)) ((D).terminal m) ((hD).2.2.1 m)).comp
      (S.iterateTerminalFactor B hB hb hS ha r₀ hr₀ (m + 1) (m + 1)).toRingHom =
    (S.iterateTerminalFactor B hB hb hS ha r₀ hr₀ m m).toRingHom.comp
      (ringMap f (S.terminal (m + 1)) (S.terminal m) (hS.2.2.1 m)) := by
  apply punctureFactor_coefficientSquare
    (a := fun b ↦ S.iterateTerminalPuncture B hB hb hS ha r₀ hr₀ (m + 1) b (m + 1))
    (d := fun b ↦ S.iterateTerminalPuncture B hB hb hS ha r₀ hr₀ m b m)
  · exact fun b ↦ S.iterateTerminalFactor_puncture B hB hb hS ha r₀ hr₀ (m + 1) (m + 1) b
  · exact fun b ↦ S.iterateTerminalFactor_puncture B hB hb hS ha r₀ hr₀ m m b
  · exact fun b ↦ S.diagonalTerminalPuncture_compatible B hB hb hS ha r₀ hr₀ b m

end FLT.Mazur.PolygonArithmeticRetainedChain

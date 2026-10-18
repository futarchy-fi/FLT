/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSimultaneousPunctureRestriction
public import FLT.Mazur.PolygonSmoothingPunctureSquare

/-!
# Coefficient squares for the sealed finite whole-node factors

The full finite Laurent substitutions are coefficient compatible. Detection
on both original punctures then proves the actual whole-node squares.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticSimultaneous
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R}
  (B : (m : ℕ) → (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])
  (hB : CompatibleEquiv B) (hb : ReciprocalBase B)
  (S : State R π) (hS : S.Compatible) (ha : S.Annihilated)
  (r₀ : ℕ) (hr₀ : S.Normalized B r₀)
local notation "P" => S.iterateAux B hB hb hS ha r₀ hr₀
local notation "F" => S.iterateSelectedFieldAux B hB hb hS ha r₀ hr₀
attribute [local irreducible] State.iterateAux State.iterateInitialFactorAux
  State.iterateLastFactorAux State.iterateTerminalFactorAux
local notation "I" => S.iterate B hB hb hS ha r₀ hr₀
local notation "hI" => S.iterate_compatible B hB hb hS ha r₀ hr₀
variable (m : ℕ)
local notation "f" => AlgHom.toRingHom (restriction R π m)



/-- The sealed finite initial comparison retains its exact coefficient square. -/
theorem State.iterateInitialFactor_restriction (b : Bool) (k : ℕ) :
    (ringMap f (S.initial (m + 1) b) (S.initial m b) (hS.1 m b)).comp
      (S.iterateInitialFactor B hB hb hS ha r₀ hr₀ k (m + 1) b).toRingHom =
    (S.iterateInitialFactor B hB hb hS ha r₀ hr₀ k m b).toRingHom.comp
      (ringMap f ((I k).initial (m + 1) b) ((I k).initial m b) ((hI k).1 m b)) := by
  apply punctureFactor_coefficientSquare
    (a := fun c ↦ S.iterateInitialPuncture B hB hb hS ha r₀ hr₀ (m + 1) b c k)
    (d := fun c ↦ S.iterateInitialPuncture B hB hb hS ha r₀ hr₀ m b c k)
  · exact fun c ↦ S.iterateInitialFactor_puncture B hB hb hS ha r₀ hr₀ k (m + 1) b c
  · exact fun c ↦ S.iterateInitialFactor_puncture B hB hb hS ha r₀ hr₀ k m b c
  · exact fun c ↦ S.iterateInitialPuncture_compatible B hB hb hS ha r₀ hr₀ b c k m

/-- The sealed finite last comparison retains its exact coefficient square. -/
theorem State.iterateLastFactor_restriction (b : Bool) (k : ℕ) :
    (ringMap f (S.last (m + 1) b) (S.last m b) (hS.2.1 m b)).comp
      (S.iterateLastFactor B hB hb hS ha r₀ hr₀ k (m + 1) b).toRingHom =
    (S.iterateLastFactor B hB hb hS ha r₀ hr₀ k m b).toRingHom.comp
      (ringMap f ((I k).last (m + 1) b) ((I k).last m b) ((hI k).2.1 m b)) := by
  apply punctureFactor_coefficientSquare
    (a := fun c ↦ S.iterateLastPuncture B hB hb hS ha r₀ hr₀ (m + 1) b c k)
    (d := fun c ↦ S.iterateLastPuncture B hB hb hS ha r₀ hr₀ m b c k)
  · exact fun c ↦ S.iterateLastFactor_puncture B hB hb hS ha r₀ hr₀ k (m + 1) b c
  · exact fun c ↦ S.iterateLastFactor_puncture B hB hb hS ha r₀ hr₀ k m b c
  · exact fun c ↦ S.iterateLastPuncture_compatible B hB hb hS ha r₀ hr₀ b c k m

/-- The sealed common terminal comparison retains the full rebased quotient square. -/
theorem State.iterateTerminalFactor_restriction (k : ℕ) :
    (ringMap f ((I k).terminal (m + 1)) ((I k).terminal m) ((hI k).2.2.1 m)).comp
      (S.iterateTerminalFactor B hB hb hS ha r₀ hr₀ k (m + 1)).toRingHom =
    (S.iterateTerminalFactor B hB hb hS ha r₀ hr₀ k m).toRingHom.comp
      (ringMap f (S.terminal (m + 1)) (S.terminal m) (hS.2.2.1 m)) := by
  apply punctureFactor_coefficientSquare
    (a := fun b ↦ S.iterateTerminalPuncture B hB hb hS ha r₀ hr₀ (m + 1) b k)
    (d := fun b ↦ S.iterateTerminalPuncture B hB hb hS ha r₀ hr₀ m b k)
  · exact fun b ↦ S.iterateTerminalFactor_puncture B hB hb hS ha r₀ hr₀ k (m + 1) b
  · exact fun b ↦ S.iterateTerminalFactor_puncture B hB hb hS ha r₀ hr₀ k m b
  · exact fun b ↦ S.iterateTerminalPuncture_compatible B hB hb hS ha r₀ hr₀ b k m

end FLT.Mazur.PolygonArithmeticSimultaneous

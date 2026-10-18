/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSimultaneousIteration
public import FLT.Mazur.PolygonSmoothingParameterEquiv

/-!
# Whole-node comparisons for the finite simultaneous construction

Compose the actual node factors along the recursively selected fields. The
initial and last comparisons point back to their seed nodes; the common
terminal comparison retains the opposite rebasing orientation. Every source
and target uses its exact accumulated smoothing.
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
local notation "I" => S.iterate B hB hb hS ha r₀ hr₀
/-- The integral fields selected by the actual finite auxiliary construction. -/
def State.iterateSelectedFieldAux (k : ℕ) : Bool → Bool → R[T;T⁻¹] :=
  let prev := P k
  prev.val.nextIntegralField B prev.property.1 hB (r₀ + k) prev.property.2.2

local notation "F" => S.iterateSelectedFieldAux B hB hb hS ha r₀ hr₀

/-- The finite initial factor is the composite on the actual intermediate node rings. -/
def State.iterateInitialFactorAux (m : ℕ) (b : Bool) : (k : ℕ) →
    ChartRing ((P k).val.initial m b) ≃ₐ[Quotient R π m] ChartRing (S.initial m b)
  | 0 => AlgEquiv.refl
  | k + 1 => ((P k).val.initialFactor (r₀ + k) (F k) m b).trans
      (State.iterateInitialFactorAux m b k)

/-- The finite last comparison uses both punctures of one whole node at every step. -/
def State.iterateLastFactorAux (m : ℕ) (b : Bool) : (k : ℕ) →
    ChartRing ((P k).val.last m b) ≃ₐ[Quotient R π m] ChartRing (S.last m b)
  | 0 => AlgEquiv.refl
  | k + 1 => ((P k).val.lastFactor (r₀ + k) (F k) m b).trans
      (State.iterateLastFactorAux m b k)

/-- The finite common terminal comparison composes every inverse smoothing drift. -/
def State.iterateTerminalFactorAux (m : ℕ) : (k : ℕ) →
    ChartRing (S.terminal m) ≃ₐ[Quotient R π m] ChartRing ((P k).val.terminal m)
  | 0 => AlgEquiv.refl
  | k + 1 => (State.iterateTerminalFactorAux m k).trans
      ((P k).val.terminalFactor (r₀ + k) (F k) m)

attribute [local irreducible] State.iterateAux State.iterateInitialFactorAux
  State.iterateLastFactorAux State.iterateTerminalFactorAux

/-- Seal the full initial comparison on the exact finite-state smoothing. -/
irreducible_def State.iterateInitialFactor (k m : ℕ) (b : Bool) :
    ChartRing ((I k).initial m b) ≃ₐ[Quotient R π m] ChartRing (S.initial m b) :=
  (nodeParameterEquiv _ _ (congrArg (fun U : State R π ↦ U.initial m b)
    (S.iterate_def B hB hb hS ha r₀ hr₀ k))).trans
      (S.iterateInitialFactorAux B hB hb hS ha r₀ hr₀ m b k)

/-- Seal the shared full last comparison on the exact finite-state smoothing. -/
irreducible_def State.iterateLastFactor (k m : ℕ) (b : Bool) :
    ChartRing ((I k).last m b) ≃ₐ[Quotient R π m] ChartRing (S.last m b) :=
  (nodeParameterEquiv _ _ (congrArg (fun U : State R π ↦ U.last m b)
    (S.iterate_def B hB hb hS ha r₀ hr₀ k))).trans
      (S.iterateLastFactorAux B hB hb hS ha r₀ hr₀ m b k)

/-- Seal the common terminal comparison on the exact finite-state smoothing. -/
irreducible_def State.iterateTerminalFactor (k m : ℕ) :
    ChartRing (S.terminal m) ≃ₐ[Quotient R π m] ChartRing ((I k).terminal m) :=
  (S.iterateTerminalFactorAux B hB hb hS ha r₀ hr₀ m k).trans
    (nodeParameterEquiv _ _ (congrArg (fun U : State R π ↦ U.terminal m)
      (S.iterate_def B hB hb hS ha r₀ hr₀ k)).symm)

end FLT.Mazur.PolygonArithmeticSimultaneous

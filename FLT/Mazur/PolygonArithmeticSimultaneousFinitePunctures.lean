/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSimultaneousPunctureIteration

/-!
# Complete puncture identities on the sealed finite simultaneous states

The explicit equal-parameter transports in the sealed node comparisons preserve
both original punctures. Thus the finite Laurent substitutions are induced by
the actual full factors on the exact finite-state smoothings.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticSimultaneous
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] State.iterateAux State.iterateInitialFactorAux
  State.iterateLastFactorAux State.iterateTerminalFactorAux
  State.iterateInitialPuncture State.iterateLastPuncture State.iterateTerminalPuncture
variable {R : Type*} [CommRing R] {π : R}
  (B : (m : ℕ) → (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])
  (hB : CompatibleEquiv B) (hb : ReciprocalBase B)
  (S : State R π) (hS : S.Compatible) (ha : S.Annihilated)
  (r₀ : ℕ) (hr₀ : S.Normalized B r₀) (k m : ℕ)
local notation "I" => S.iterate B hB hb hS ha r₀ hr₀ k
local notation "A" => S.iterateInitialFactor B hB hb hS ha r₀ hr₀ k m
local notation "L" => S.iterateLastFactor B hB hb hS ha r₀ hr₀ k m
local notation "T" => S.iterateTerminalFactor B hB hb hS ha r₀ hr₀ k m
local notation "a" => S.iterateInitialPuncture B hB hb hS ha r₀ hr₀ m
local notation "l" => S.iterateLastPuncture B hB hb hS ha r₀ hr₀ m
local notation "t" => S.iterateTerminalPuncture B hB hb hS ha r₀ hr₀ m

/-- Both finite initial substitutions are induced by the actual sealed initial node factor. -/
theorem State.iterateInitialFactor_puncture (b c : Bool) :
    (punctureLaurentMap (S.initial m b) c).comp (A b).toAlgHom =
      (a b c k).toAlgHom.comp (punctureLaurentMap ((I).initial m b) c) := by
  rw [State.iterateInitialFactor_def]
  change (punctureLaurentMap _ c).comp
    ((S.iterateInitialFactorAux B hB hb hS ha r₀ hr₀ m b k).toAlgHom.comp
      (nodeParameterEquiv _ _ _).toAlgHom) = _
  rw [← AlgHom.comp_assoc, State.iterateInitialFactorAux_puncture,
    AlgHom.comp_assoc, punctureLaurentMap_parameter]

/-- Both finite last substitutions come from the same actual full shared last-node factor. -/
theorem State.iterateLastFactor_puncture (b c : Bool) :
    (punctureLaurentMap (S.last m b) c).comp (L b).toAlgHom =
      (l b c k).toAlgHom.comp (punctureLaurentMap ((I).last m b) c) := by
  rw [State.iterateLastFactor_def]
  change (punctureLaurentMap _ c).comp
    ((S.iterateLastFactorAux B hB hb hS ha r₀ hr₀ m b k).toAlgHom.comp
      (nodeParameterEquiv _ _ _).toAlgHom) = _
  rw [← AlgHom.comp_assoc, State.iterateLastFactorAux_puncture,
    AlgHom.comp_assoc, punctureLaurentMap_parameter]

/-- Both finite terminal substitutions come from the actual common rebased terminal factor. -/
theorem State.iterateTerminalFactor_puncture (b : Bool) :
    (punctureLaurentMap ((I).terminal m) b).comp (T).toAlgHom =
      (t b k).toAlgHom.comp (punctureLaurentMap (S.terminal m) b) := by
  rw [State.iterateTerminalFactor_def]
  change (punctureLaurentMap _ b).comp ((nodeParameterEquiv _ _ _).toAlgHom.comp
    (S.iterateTerminalFactorAux B hB hb hS ha r₀ hr₀ m k).toAlgHom) = _
  rw [← AlgHom.comp_assoc, punctureLaurentMap_parameter,
    State.iterateTerminalFactorAux_puncture]

end FLT.Mazur.PolygonArithmeticSimultaneous

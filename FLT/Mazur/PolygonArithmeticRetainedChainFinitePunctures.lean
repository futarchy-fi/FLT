/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainPunctureIteration

/-!
# Complete puncture identities on the finite retained-chain states

The explicit equal-parameter transports in the sealed node comparisons preserve
both original punctures. Thus the finite Laurent substitutions are induced by
the actual full factors on the exact finite-state smoothings.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticRetainedChain
open PolygonArithmeticStages PolygonArithmeticSimultaneous PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] State.iterateAux State.iterateInitialFactorAux
  State.iterateRetainedFactorAux State.iterateTerminalFactorAux
  State.iterateInitialPuncture State.iterateRetainedPuncture State.iterateTerminalPuncture
variable {R : Type*} [CommRing R] {π : R} {n : ℕ}
  (B : (m : ℕ) → (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])
  (hB : CompatibleEquiv B) (hb : ReciprocalBase B)
  (S : State R π n) (hS : S.Compatible) (ha : S.Annihilated)
  (r₀ : ℕ) (hr₀ : S.Normalized B r₀) (k m : ℕ)
local notation "I" => S.iterate B hB hb hS ha r₀ hr₀ k
local notation "A" => S.iterateInitialFactor B hB hb hS ha r₀ hr₀ k m
local notation "L" => S.iterateRetainedFactor B hB hb hS ha r₀ hr₀ k m
local notation "T" => S.iterateTerminalFactor B hB hb hS ha r₀ hr₀ k m
local notation "a" => S.iterateInitialPuncture B hB hb hS ha r₀ hr₀ m
local notation "l" => S.iterateRetainedPuncture B hB hb hS ha r₀ hr₀ m
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

/-- Both finite retained substitutions come from the same complete retained-node factor. -/
theorem State.iterateRetainedFactor_puncture (i : Fin (n + 1)) (b c : Bool) :
    (punctureLaurentMap (S.retained m i b) c).comp (L i b).toAlgHom =
      (l i b c k).toAlgHom.comp (punctureLaurentMap ((I).retained m i b) c) := by
  rw [State.iterateRetainedFactor_def]
  change (punctureLaurentMap _ c).comp
    ((S.iterateRetainedFactorAux B hB hb hS ha r₀ hr₀ m i b k).toAlgHom.comp
      (nodeParameterEquiv _ _ _).toAlgHom) = _
  rw [← AlgHom.comp_assoc, State.iterateRetainedFactorAux_puncture,
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

end FLT.Mazur.PolygonArithmeticRetainedChain

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainPunctureStability
public import FLT.Mazur.PolygonArithmeticRetainedChainIterationStability
public import FLT.Mazur.PolygonArithmeticRetainedChainFinitePunctures

/-!
# Stabilization of the complete finite whole-node comparisons

The full accumulated factors stabilize after canonical transport of their
actual equal smoothings. Detection uses both complete punctures of each node.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticRetainedChain
open PolygonArithmeticStages PolygonArithmeticSimultaneous PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] State.iterateAux
variable {R : Type*} [CommRing R] {π : R} {n : ℕ}
  (B : (m : ℕ) → (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])
  (hB : CompatibleEquiv B) (hb : ReciprocalBase B)
  (S : State R π n) (hS : S.Compatible) (ha : S.Annihilated)
  (r₀ : ℕ) (hr₀ : S.Normalized B r₀) {k l m : ℕ} (hkl : k ≤ l) (hm : m ≤ r₀ + k)

/-- The whole finite initial comparison stabilizes with its actual source smoothing. -/
theorem State.iterateInitialFactor_stable (b : Bool) :
    S.iterateInitialFactor B hB hb hS ha r₀ hr₀ l m b =
      (nodeParameterEquiv _ _
        (S.iterate_initial_stable B hB hb hS ha r₀ hr₀ hkl hm b)).trans
          (S.iterateInitialFactor B hB hb hS ha r₀ hr₀ k m b) := by
  apply nodeFactor_eq_of_punctures
  intro c
  change (punctureLaurentMap _ c).comp _ = (punctureLaurentMap _ c).comp
    ((S.iterateInitialFactor B hB hb hS ha r₀ hr₀ k m b).toAlgHom.comp
      (nodeParameterEquiv _ _ _).toAlgHom)
  rw [← AlgHom.comp_assoc, State.iterateInitialFactor_puncture,
    State.iterateInitialFactor_puncture, AlgHom.comp_assoc, punctureLaurentMap_parameter,
    S.iterateInitialPuncture_stable B hB hb hS ha r₀ hr₀ m hkl hm]

/-- The whole finite retained comparison stabilizes with its actual source smoothing. -/
theorem State.iterateRetainedFactor_stable (i : Fin (n + 1)) (b : Bool) :
    S.iterateRetainedFactor B hB hb hS ha r₀ hr₀ l m i b =
      (nodeParameterEquiv _ _
        (S.iterate_retained_stable B hB hb hS ha r₀ hr₀ hkl hm i b)).trans
          (S.iterateRetainedFactor B hB hb hS ha r₀ hr₀ k m i b) := by
  apply nodeFactor_eq_of_punctures
  intro c
  change (punctureLaurentMap _ c).comp _ = (punctureLaurentMap _ c).comp
    ((S.iterateRetainedFactor B hB hb hS ha r₀ hr₀ k m i b).toAlgHom.comp
      (nodeParameterEquiv _ _ _).toAlgHom)
  rw [← AlgHom.comp_assoc, State.iterateRetainedFactor_puncture,
    State.iterateRetainedFactor_puncture, AlgHom.comp_assoc, punctureLaurentMap_parameter,
    S.iterateRetainedPuncture_stable B hB hb hS ha r₀ hr₀ m hkl hm]

/-- The common terminal comparison stabilizes with its full rebased target smoothing. -/
theorem State.iterateTerminalFactor_stable :
    S.iterateTerminalFactor B hB hb hS ha r₀ hr₀ l m =
      (S.iterateTerminalFactor B hB hb hS ha r₀ hr₀ k m).trans
        (nodeParameterEquiv _ _
          (S.iterate_terminal_stable B hB hb hS ha r₀ hr₀ hkl hm).symm) := by
  apply nodeFactor_eq_of_punctures
  intro b
  change (punctureLaurentMap _ b).comp _ = (punctureLaurentMap _ b).comp
    ((nodeParameterEquiv _ _ _).toAlgHom.comp
      (S.iterateTerminalFactor B hB hb hS ha r₀ hr₀ k m).toAlgHom)
  rw [← AlgHom.comp_assoc, punctureLaurentMap_parameter,
    State.iterateTerminalFactor_puncture, State.iterateTerminalFactor_puncture,
    S.iterateTerminalPuncture_stable B hB hb hS ha r₀ hr₀ m hkl hm]

end FLT.Mazur.PolygonArithmeticRetainedChain

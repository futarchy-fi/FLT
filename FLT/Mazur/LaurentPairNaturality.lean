/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentPairEvaluation

/-!
# Naturality of full Laurent evaluation

Changing coefficients and mapping the target commute with evaluating at units.
The formulas use ring homomorphisms so that all coefficient towers are explicit.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentPairNaturality
open LaurentPolynomial PolygonScalingNaturality
variable {R S B D : Type*} [CommRing R] [CommRing S] [CommRing B] [CommRing D]

/-- Mapping a Laurent evaluation maps its coefficients and its unit input. -/
theorem eval₂_map (f : R →+* B) (g : B →+* D) (u : Bˣ) :
    g.comp (eval₂ f u) = eval₂ (g.comp f) (Units.map g.toMonoidHom u) := by
  apply ringHom_ext <;> simp [eval₂_C, eval₂_T]

/-- Changing Laurent coefficients before evaluation composes the coefficient maps. -/
theorem eval₂_coeffMap (f : R →+* S) (g : S →+* B) (u : Bˣ) :
    (eval₂ g u).comp (coeffMap f) = eval₂ (g.comp f) u := by
  apply ringHom_ext <;> simp [eval₂_C, eval₂_T]

/-- Evaluate a pair of Laurent variables with an explicit map on the scalar coefficients. -/
def pairEval₂ (f : R →+* B) (u v : Bˣ) : R[T;T⁻¹][T;T⁻¹] →+* B :=
  eval₂ (eval₂ f u) v

/-- Two-variable evaluation commutes with every target ring homomorphism. -/
theorem pairEval₂_map (f : R →+* B) (g : B →+* D) (u v : Bˣ) :
    g.comp (pairEval₂ f u v) =
      pairEval₂ (g.comp f) (Units.map g.toMonoidHom u) (Units.map g.toMonoidHom v) := by
  unfold pairEval₂
  rw [eval₂_map, eval₂_map]

/-- Both levels of coefficient change commute with evaluation. -/
theorem pairEval₂_coeffMap (f : R →+* S) (g : S →+* B) (u v : Bˣ) :
    (pairEval₂ g u v).comp (coeffMap (coeffMap f)) = pairEval₂ (g.comp f) u v := by
  unfold pairEval₂
  rw [eval₂_coeffMap, eval₂_coeffMap]

/-- The explicit coefficient formulation agrees with the coefficient-algebra formulation. -/
theorem pairEval₂_algebra [Algebra R B] (u v : Bˣ) :
    pairEval₂ (algebraMap R B) u v = (LaurentPairEvaluation.pairEval u v).toRingHom := rfl

end FLT.Mazur.LaurentPairNaturality

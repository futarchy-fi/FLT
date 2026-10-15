/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentWeightedEvaluation
public import Mathlib.Tactic.LinearCombination

/-!
# The cocycle equation forced by an associative square-zero perturbation

An actual associative unit law with Laurent error eP, where e squared is zero,
forces the weighted multiplicative cocycle equation for P. The conclusion
retains e; cancellation requires a separate faithful top-layer argument.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentSquareZeroCocycle
open LaurentPairEvaluation LaurentWeightedEvaluation
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable (e : B) (he : e ^ 2 = 0) (p : R[T;T⁻¹][T;T⁻¹])
variable (M : Bˣ → Bˣ → Bˣ)
variable (hM : ∀ u v, (M u v).val = u.val * v.val + e * pairEval u v p)
include he hM

/-- The perturbed product and ordinary product agree modulo the weight's annihilator. -/
theorem weighted_product (u v : Bˣ) : e * (M u v).val = e * (u * v).val := by
  rw [hM, mul_add, ← mul_assoc e e, ← pow_two, he, zero_mul, add_zero, Units.val_mul]

/-- In the weighted error term the inner perturbed product can be replaced on the left. -/
theorem weighted_left (u v w : Bˣ) :
    e * pairEval (M u v) w p = e * pairEval (u * v) w p :=
  weighted_pairEval e _ _ _ _ (weighted_product e he p M hM u v) rfl p

/-- The same replacement is valid in the right inner input. -/
theorem weighted_right (u v w : Bˣ) :
    e * pairEval u (M v w) p = e * pairEval u (v * w) p :=
  weighted_pairEval e _ _ _ _ rfl (weighted_product e he p M hM v w) p

/-- Associativity of the original perturbed law forces its weighted cocycle equation. -/
theorem cocycle (hassoc : ∀ u v w, M (M u v) w = M u (M v w)) (u v w : Bˣ) :
    e * (w.val * pairEval u v p + pairEval (u * v) w p) =
      e * (u.val * pairEval v w p + pairEval u (v * w) p) := by
  have ha := congrArg Units.val (hassoc u v w)
  simp only [hM] at ha
  rw [weighted_left e he p M hM, weighted_right e he p M hM] at ha
  linear_combination ha

end FLT.Mazur.LaurentSquareZeroCocycle

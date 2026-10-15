/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentSquareZeroCocycle
public import FLT.Mazur.PolygonCompleteIdentityPointDefect

/-!
# The actual first-order multiplication obstruction satisfies a weighted cocycle

Associativity of the original finite point law applies on every coefficient
algebra. Its canonical error therefore satisfies the square-zero cocycle
identity, with no assumption that the first positive-order law already holds.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPairEvaluation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
variable (B : Type) [CommRing B] [Algebra (Ring K 1) B]
local notation "P" => completeIdentityFirstObstructionLift K n h i
local notation "e" => algebraMap (Ring K 1) B (parameter K 1)

/-- The original first reduced error obeys the weighted cocycle identity on every algebra. -/
theorem completeIdentityFirstObstructionLift_cocycle (u v w : Bˣ) :
    (e) * (w.val * pairEval u v (P) + pairEval (u * v) w (P)) =
      (e) * (u.val * pairEval v w (P) + pairEval u (v * w) (P)) :=
  LaurentSquareZeroCocycle.cocycle (e) (completeIdentityFirstWeight_sq K B) (P)
    (completeIdentityFinitePointMul K n h i 1 B)
    (completeIdentityFinitePointMul_one_val K n h i B)
    (completeIdentityFinitePointMul_assoc K n h i 1 B) u v w

end FLT.Mazur.PolygonInfinitesimalStages

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityPointDefect
public import FLT.Mazur.LaurentSquareZeroCocycle
public import FLT.Mazur.PolygonStageTopScalar

/-!
# Weighted original multiplication cocycles at every successive order

Once the preceding original law is proved, the next original point product
is a square-zero perturbation by its actual top coefficient. Associativity
therefore gives the weighted cocycle on every coefficient algebra.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial LaurentUnitPoints LaurentPairEvaluation PolygonScalingNaturality
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)

/-- Lift the canonical next obstruction without changing either original Laurent variable. -/
def completeIdentityTopObstructionLift : (Ring K (m + 1))[T;T⁻¹][T;T⁻¹] :=
  coeffMap (coeffMap (algebraMap K (Ring K (m + 1))))
    (completeIdentityFiniteMulObstruction K n h i m)
local notation "P" => completeIdentityTopObstructionLift K n h i m

/-- The unchanged next point product is its exact top-layer perturbation of multiplication. -/
theorem completeIdentityFinitePointMul_top_val
    (hm : completeIdentityFiniteMulDefect K n h i m = 0)
    (B : Type) [CommRing B] [Algebra (Ring K (m + 1)) B] (u v : Bˣ) :
    (completeIdentityFinitePointMul K n h i (m + 1) B u v).val = u.val * v.val +
      algebraMap (Ring K (m + 1)) B (parameter K (m + 1)) ^ (m + 1) *
        pairEval u v (P) := by
  rw [completeIdentityFinitePointMul_val,
    completeIdentityFiniteMulDefect_from_obstruction K n h i m hm]
  simp only [map_mul, map_pow, pairEval_C, evalUnit_C]
  rfl

/-- Every next original obstruction satisfies the weighted cocycle before top-layer extraction. -/
theorem completeIdentityTopObstructionLift_cocycle
    (hm : completeIdentityFiniteMulDefect K n h i m = 0)
    (B : Type) [CommRing B] [Algebra (Ring K (m + 1)) B] (u v w : Bˣ) :
    algebraMap (Ring K (m + 1)) B (parameter K (m + 1)) ^ (m + 1) *
        (w.val * pairEval u v (P) + pairEval (u * v) w (P)) =
      algebraMap (Ring K (m + 1)) B (parameter K (m + 1)) ^ (m + 1) *
        (u.val * pairEval v w (P) + pairEval u (v * w) (P)) :=
  LaurentSquareZeroCocycle.cocycle _ (parameter_top_weight_sq K m B) (P)
    (completeIdentityFinitePointMul K n h i (m + 1) B)
    (completeIdentityFinitePointMul_top_val K n h i m hm B)
    (completeIdentityFinitePointMul_assoc K n h i (m + 1) B) u v w

end FLT.Mazur.PolygonInfinitesimalStages

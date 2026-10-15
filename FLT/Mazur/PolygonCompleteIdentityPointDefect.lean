/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFinitePointLaw
public import FLT.Mazur.PolygonCompleteIdentityTopObstruction

/-!
# Evaluating the actual multiplication error on arbitrary algebra points

The original finite point law is ordinary multiplication plus evaluation of
its exact error. At order one that error is the smoothing parameter times
the lifted canonical reduced obstruction, without an unproved lower-order law.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial LaurentUnitPoints LaurentPairEvaluation PolygonScalingNaturality
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)

/-- The actual point product differs from the ordinary unit product by the evaluated full error. -/
theorem completeIdentityFinitePointMul_val (m : ℕ) (B : Type) [CommRing B]
    [Algebra (Ring K m) B] (u v : Bˣ) :
    (completeIdentityFinitePointMul K n h i m B u v).val = u.val * v.val +
      pairEval u v (completeIdentityFiniteMulDefect K n h i m) := by
  change pairEval u v (completeIdentityFiniteMulUnit K n h i m).val = _
  rw [completeIdentityFiniteMulDefect, map_sub, map_mul, pairEval_C,
    evalUnit_T, pairEval_T, zpow_one, zpow_one]
  ring

/-- The lifted first reduced obstruction, with both original Laurent variables retained. -/
def completeIdentityFirstObstructionLift : (Ring K 1)[T;T⁻¹][T;T⁻¹] :=
  coeffMap (coeffMap (algebraMap K (Ring K 1)))
    (completeIdentityFiniteMulObstruction K n h i 0)

/-- The order-one point law has the actual canonical square-zero correction on every algebra. -/
theorem completeIdentityFinitePointMul_one_val (B : Type) [CommRing B]
    [Algebra (Ring K 1) B] (u v : Bˣ) :
    (completeIdentityFinitePointMul K n h i 1 B u v).val = u.val * v.val +
      algebraMap (Ring K 1) B (parameter K 1) *
        pairEval u v (completeIdentityFirstObstructionLift K n h i) := by
  rw [completeIdentityFinitePointMul_val,
    completeIdentityFiniteMulDefect_from_obstruction K n h i 0
      (completeIdentityFiniteMulDefect_zero K n h i)]
  simp only [zero_add, pow_one, map_mul, pairEval_C, evalUnit_C]
  rfl

/-- The first smoothing weight is square-zero on every coefficient algebra. -/
theorem completeIdentityFirstWeight_sq (B : Type) [CommRing B] [Algebra (Ring K 1) B] :
    algebraMap (Ring K 1) B (parameter K 1) ^ 2 = 0 := by
  rw [← map_pow, parameter_pow K 1, map_zero]

end FLT.Mazur.PolygonInfinitesimalStages

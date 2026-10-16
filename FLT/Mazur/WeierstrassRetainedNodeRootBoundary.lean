/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedNodeRoots
public import FLT.Mazur.WeierstrassModificationXNodeInverseEvaluation

/-!
# The full retained node roots recover the original Laurent branches

On the original right puncture, x becomes π T⁻¹. The first and second powers
of π in the divided coefficients recover the unchanged initial equations.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (π : R)

/-- Evaluation on the actual right puncture of the entire retained node. -/
def retainedRightEvaluation : ChartRing π →ₐ[R] R[T;T⁻¹] :=
  (leftLaurentMap π).comp (branchSwapMap π)

/-- The left coordinate retains its original smoothing factor on the right puncture. -/
theorem retainedRightEvaluation_left :
    retainedRightEvaluation π (leftCoordinate π) =
      LaurentPolynomial.C π * LaurentPolynomial.T (-1) := by
  simp only [retainedRightEvaluation, AlgHom.comp_apply, branchSwapMap_left,
    leftLaurentMap_right]

/-- The right coordinate is exactly the original Laurent parameter. -/
theorem retainedRightEvaluation_right :
    retainedRightEvaluation π (rightCoordinate π) = LaurentPolynomial.T 1 := by
  simp only [retainedRightEvaluation, AlgHom.comp_apply, branchSwapMap_right,
    leftLaurentMap_left]

variable (W : WeierstrassCurve R) (s c3 c4 c6 : R) (I : Ideal R) (hI : IsNilpotent I)
  (ha : IsUnit W.a₁) (hs : s ∈ I) (h2 : W.a₂ ∈ I)
  (h3 : c3 ∈ I) (h4 : c4 ∈ I) (h6 : c6 ∈ I)
local notation "E" => retainedRightEvaluation π
local notation "J" => I.map (algebraMap R (ChartRing π))
local notation "L" => laurentArithmeticIdeal I
local notation "b3" => π * c3
local notation "b4" => π * c4
local notation "b6" => π ^ 2 * c6
local notation "H3" => I.mul_mem_left π h3
local notation "H4" => I.mul_mem_left π h4
local notation "H6" => I.mul_mem_left (π ^ 2) h6

/-- The entire right-puncture evaluation preserves the original nilpotent coefficient ideal. -/
theorem retainedRightEvaluation_ideal : J ≤ (L).comap (E).toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  change E (algebraMap R _ a) ∈ L
  rw [AlgHom.commutes]
  exact Ideal.mem_map_of_mem _ ha

/-- The regular retained linear coefficient restricts to the original full Laurent one. -/
theorem retainedSlopeLinear_right :
    E (retainedSlopeLinear W π c3) = laurentSlopeLinear W b3 := by
  simp only [retainedSlopeLinear, map_add, map_mul, AlgHom.commutes,
    retainedRightEvaluation_left, laurentSlopeLinear, map_mul]
  change LaurentPolynomial.C W.a₁ + LaurentPolynomial.C c3 *
    (LaurentPolynomial.C π * LaurentPolynomial.T (-1)) = _
  ring

/-- The full retained slope constant restricts with both original parameter powers intact. -/
theorem retainedSlopeConstant_right :
    E (retainedSlopeConstant W π s c4 c6) = laurentSlopeConstant W s b4 b6 := by
  simp only [retainedSlopeConstant, retainedConicConstant, map_add, map_mul, map_pow,
    AlgHom.commutes, retainedRightEvaluation_left, retainedRightEvaluation_right,
    laurentSlopeConstant]
  simp only [show algebraMap R R[T;T⁻¹] = LaurentPolynomial.C from rfl]
  ring

/-- The constructed full node root is the independently constructed original Laurent slope. -/
theorem retainedSlopeRoot_right :
    E (retainedSlopeRoot W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6) =
      nilpotentLaurentSlope W s b3 b4 b6 I hI ha hs h2 H3 H4 H6 := by
  apply NilpotentQuadraticRoot.root_unique L (laurentArithmeticIdeal_nilpotent I hI)
    (laurentSlopeLinear W b3) (laurentSlopeConstant W s b4 b6)
    (laurentSlopeLinear_unit W b3 I hI ha H3)
  · exact retainedRightEvaluation_ideal π I
      (retainedSlopeRoot_mem W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6)
  · exact nilpotentLaurentSlope_mem W s b3 b4 b6 I hI ha hs h2 H3 H4 H6
  · have he := congrArg E (retainedSlopeRoot_equation W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6)
    simpa only [map_add, map_mul, map_pow, retainedSlopeLinear_right,
      retainedSlopeConstant_right] using he
  · exact nilpotentLaurentSlope_equation ..

/-- The retained conic constant has precisely the divided original polynomial restriction. -/
theorem retainedConicConstant_right :
    E (retainedConicConstant W π c4 c6) =
      LaurentPolynomial.C W.a₂ + LaurentPolynomial.C b4 * LaurentPolynomial.T (-1) +
        LaurentPolynomial.C b6 * LaurentPolynomial.T (-1) ^ 2 := by
  simp only [retainedConicConstant, map_add, map_mul, map_pow, AlgHom.commutes,
    retainedRightEvaluation_left]
  simp only [show algebraMap R R[T;T⁻¹] = LaurentPolynomial.C from rfl]
  ring

local notation "r" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 H3 H4 H6
attribute [local irreducible] polynomialSlopeRoot retainedConicRoot

/-- The second constructed node root recovers the full independently constructed conic root. -/
theorem retainedConicRoot_right :
    E (retainedConicRoot W π c3 c4 c6 I hI ha h2 h3 h4 h6) =
      (r).eval₂ (algebraMap R R[T;T⁻¹]) (LaurentPolynomial.T (-1)) := by
  apply NilpotentQuadraticRoot.root_unique (L) (laurentArithmeticIdeal_nilpotent I hI)
    (laurentSlopeLinear W b3)
    (LaurentPolynomial.C W.a₂ + LaurentPolynomial.C b4 * LaurentPolynomial.T (-1) +
      LaurentPolynomial.C b6 * LaurentPolynomial.T (-1) ^ 2)
    (laurentSlopeLinear_unit W b3 I hI ha H3)
  · exact retainedRightEvaluation_ideal π I
      (retainedConicRoot_mem W π c3 c4 c6 I hI ha h2 h3 h4 h6)
  · exact NilpotentPolynomialInverse.eval₂_mem I _ r
      (polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 H3 H4 H6) _
  · have he := congrArg E (retainedConicRoot_equation W π c3 c4 c6 I hI ha h2 h3 h4 h6)
    simpa only [map_add, map_mul, map_pow, retainedSlopeLinear_right,
      retainedConicConstant_right] using he
  · exact polynomialRoot_eval_equation W b3 b4 b6 r
      (polynomialSlopeRoot_equation W b3 b4 b6 I hI ha h2 H3 H4 H6) _

end FLT.Mazur.WeierstrassModificationX

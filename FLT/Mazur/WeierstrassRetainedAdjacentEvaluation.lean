/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedNodeRootBoundary
public import FLT.Mazur.WeierstrassRetainedNodeRootsNaturality

/-!
# Entire equations on an adjacent retained Laurent edge

The next node divides its three coefficients by π, π, and π², and multiplies
its smoothing by π. Its inverse right coordinate then matches the old left edge.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (π : R)

/-- The entire right boundary in the inverse coordinate used for adjacent retained charts. -/
def retainedPrecedingEvaluation : ChartRing π →ₐ[R] R[T;T⁻¹] :=
  LaurentPolynomial.invert.toAlgHom.comp (retainedRightEvaluation π)

/-- The next left coordinate keeps the original factor of π on the shared edge. -/
theorem retainedPrecedingEvaluation_left :
    retainedPrecedingEvaluation π (leftCoordinate π) =
      LaurentPolynomial.C π * LaurentPolynomial.T 1 := by
  simp only [retainedPrecedingEvaluation, AlgHom.comp_apply, retainedRightEvaluation_left,
    AlgEquiv.coe_toAlgHom, map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
    neg_neg]

/-- The next right coordinate is the inverse of the old outgoing coordinate. -/
theorem retainedPrecedingEvaluation_right :
    retainedPrecedingEvaluation π (rightCoordinate π) = LaurentPolynomial.T (-1) := by
  simp only [retainedPrecedingEvaluation, AlgHom.comp_apply, retainedRightEvaluation_right,
    AlgEquiv.coe_toAlgHom, LaurentPolynomial.invert_T]

variable (W : WeierstrassCurve R) (s c3 c4 c6 : R)
local notation "E" => leftLaurentMap π
local notation "N" => retainedPrecedingEvaluation π

/-- The two full linear coefficients agree after the original divided-coefficient step. -/
theorem retainedSlopeLinear_adjacent :
    E (retainedSlopeLinear W π (π * c3)) = N (retainedSlopeLinear W π c3) := by
  simp only [retainedSlopeLinear, map_add, map_mul, AlgHom.commutes,
    leftLaurentMap_left, retainedPrecedingEvaluation_left]
  simp only [show algebraMap R R[T;T⁻¹] = LaurentPolynomial.C from rfl]
  ring

/-- The whole conic constant agrees with both original division powers intact. -/
theorem retainedConicConstant_adjacent :
    E (retainedConicConstant W π (π * c4) (π ^ 2 * c6)) =
      N (retainedConicConstant W π c4 c6) := by
  simp only [retainedConicConstant, map_add, map_mul, map_pow, AlgHom.commutes,
    leftLaurentMap_left, retainedPrecedingEvaluation_left]
  simp only [show algebraMap R R[T;T⁻¹] = LaurentPolynomial.C from rfl]
  ring

/-- Adjacent full slope constants agree with the next smoothing exactly π times the old one. -/
theorem retainedSlopeConstant_adjacent :
    E (retainedSlopeConstant W π s (π * c4) (π ^ 2 * c6)) =
      N (retainedSlopeConstant W π (π * s) c4 c6) := by
  simp only [retainedSlopeConstant, map_add, map_mul, AlgHom.commutes,
    retainedConicConstant_adjacent, leftLaurentMap_right, retainedPrecedingEvaluation_right]
  simp only [show algebraMap R R[T;T⁻¹] = LaurentPolynomial.C from rfl]
  ring

/-- Every full node evaluation preserves the extended arithmetic ideal. -/
theorem retainedLaurentEvaluation_ideal (I : Ideal R)
    (e : ChartRing π →ₐ[R] R[T;T⁻¹]) :
    I.map (algebraMap R (ChartRing π)) ≤ (laurentArithmeticIdeal I).comap e.toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  change e (algebraMap R _ a) ∈ laurentArithmeticIdeal I
  rw [AlgHom.commutes]
  exact Ideal.mem_map_of_mem _ ha

end FLT.Mazur.WeierstrassModificationX

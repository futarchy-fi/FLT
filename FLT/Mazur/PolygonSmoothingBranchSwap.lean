/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingLeftPuncture

/-!
# Branch interchange and the second punctured smoothing branch

The symmetry of xy = t exchanges the two actual localizations. Transporting
the first Laurent presentation gives y = z and x = t/z on the second branch.
-/

@[expose] public noncomputable section

open scoped LaurentPolynomial

namespace FLT.Mazur.PolygonSmoothing

variable {R : Type*} [CommRing R]

/-- Interchange the original two coordinates without changing the smoothing parameter. -/
def branchSwapMap (t : R) : ChartRing t →ₐ[R] ChartRing t :=
  evaluate t (rightCoordinate t) (leftCoordinate t) (by
    rw [mul_comm, coordinate_relation])

/-- Branch interchange sends the first coordinate to the second. -/
@[simp] theorem branchSwapMap_left (t : R) :
    branchSwapMap t (leftCoordinate t) = rightCoordinate t := evaluate_left ..

/-- Branch interchange sends the second coordinate to the first. -/
@[simp] theorem branchSwapMap_right (t : R) :
    branchSwapMap t (rightCoordinate t) = leftCoordinate t := evaluate_right ..

/-- Interchanging branches twice is the identity on the entire chart algebra. -/
theorem branchSwapMap_comp (t : R) :
    (branchSwapMap t).comp (branchSwapMap t) = AlgHom.id R _ := by
  apply chartRing_hom_ext t <;> simp

/-- The actual branch interchange algebra automorphism. -/
def branchSwap (t : R) : ChartRing t ≃ₐ[R] ChartRing t :=
  AlgEquiv.ofAlgHom (branchSwapMap t) (branchSwapMap t)
    (branchSwapMap_comp t) (branchSwapMap_comp t)

/-- The localization away from the original second coordinate. -/
abbrev RightPuncture (t : R) := Localization.Away (rightCoordinate t)

/-- Branch interchange identifies the two actual punctured coordinate rings. -/
def rightToLeftPuncture (t : R) : RightPuncture t ≃ₐ[R] LeftPuncture t :=
  IsLocalization.algEquivOfAlgEquiv (RightPuncture t) (LeftPuncture t)
    (M := Submonoid.powers (rightCoordinate t))
    (T := Submonoid.powers (leftCoordinate t)) (branchSwap t) (by
    rw [Submonoid.map_powers]
    change Submonoid.powers (branchSwapMap t (rightCoordinate t)) = _
    rw [branchSwapMap_right])

/-- The puncture comparison extends the original chart automorphism. -/
@[simp] theorem rightToLeftPuncture_map (t : R) (a : ChartRing t) :
    rightToLeftPuncture t (algebraMap (ChartRing t) _ a) =
      algebraMap (ChartRing t) _ (branchSwapMap t a) :=
  IsLocalization.algEquivOfAlgEquiv_eq _ a

/-- The second punctured branch is also the Laurent algebra over the original base. -/
def rightPunctureEquiv (t : R) : RightPuncture t ≃ₐ[R] R[T;T⁻¹] :=
  (rightToLeftPuncture t).trans (leftPunctureEquiv t)

/-- The second-branch Laurent variable is the original second coordinate. -/
@[simp] theorem rightPunctureEquiv_right (t : R) :
    rightPunctureEquiv t (algebraMap (ChartRing t) _ (rightCoordinate t)) =
      LaurentPolynomial.T 1 := by
  change leftPunctureToLaurent t (rightToLeftPuncture t _) = _
  rw [rightToLeftPuncture_map, branchSwapMap_right,
    leftPunctureToLaurent_map, leftLaurentMap_left]

/-- The original first coordinate becomes t divided by the second Laurent variable. -/
@[simp] theorem rightPunctureEquiv_left (t : R) :
    rightPunctureEquiv t (algebraMap (ChartRing t) _ (leftCoordinate t)) =
      LaurentPolynomial.C t * LaurentPolynomial.T (-1) := by
  change leftPunctureToLaurent t (rightToLeftPuncture t _) = _
  rw [rightToLeftPuncture_map, branchSwapMap_left,
    leftPunctureToLaurent_map, leftLaurentMap_right]

end FLT.Mazur.PolygonSmoothing

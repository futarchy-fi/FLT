/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentPositivePart
public import FLT.Mazur.PolygonFirstNodePolynomialExtension

/-!
# Constructed node extensions and their exact Laurent boundary error

Every Laurent field gives a concrete node automorphism by extending its
strictly positive part. Its restriction agrees with the desired coordinate
exactly when the omitted nonpositive tail vanishes. The error is computed
over the full original smoothing ring, rather than only after reduction.
-/

@[expose] public noncomputable section
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentPositivePart PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable {R : Type} [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "B" => ChartRing (e)

/-- A concrete node automorphism extending every strictly positive term of the given field. -/
def firstNodePositiveExtension (q : R[T;T⁻¹]) : (B) ≃ₐ[S] (B) :=
  firstNodePolynomialExtension (positivePart q) 0 (positivePart_coeff_zero q) (by rfl)

/-- Its reduction is the original node identity on all functions. -/
theorem firstNodePositiveExtension_reduction (q : R[T;T⁻¹]) (z : B) :
    firstNodeReduction R (firstNodePositiveExtension q z) = firstNodeReduction R z :=
  firstNodePolynomialExtension_reduction _ _ _ _ z

/-- Its Laurent restriction retains exactly the constructed positive part. -/
theorem firstNodePositiveExtension_leftLaurent (q : R[T;T⁻¹]) :
    leftLaurentMap (e) (firstNodePositiveExtension q (leftCoordinate (e))) =
      firstOrderLaurentCoordinate (positivePart q).toLaurent :=
  firstNodePolynomialExtension_leftLaurent _ _ _ _

/-- The original smoothing coefficient detects every coefficient of a Laurent vector field. -/
theorem firstOrderLaurentCoordinate_injective :
    Function.Injective (firstOrderLaurentCoordinate (R := R)) := by
  intro p q he
  ext d
  have hd := congrArg (fun a : (S)[T;T⁻¹] ↦ a.coeff d) he
  rw [firstOrderLaurentCoordinate_coeff, firstOrderLaurentCoordinate_coeff] at hd
  exact parameter_scalar_one_injective (add_left_cancel hd)

/-- The exact error of the constructed extension is its original nonpositive Laurent tail. -/
theorem firstNodePositiveExtension_error (q : R[T;T⁻¹]) :
    (firstOrderCoordinateUnit q).val -
        leftLaurentMap (e) (firstNodePositiveExtension q (leftCoordinate (e))) =
      C (e) * coeffMap (algebraMap R (S)) (boundaryTail q) := by
  rw [firstOrderCoordinateUnit_val, firstNodePositiveExtension_leftLaurent]
  simp only [firstOrderLaurentCoordinate, boundaryTail, map_sub, mul_sub]
  ring

/-- The constructed automorphism extends the full original coordinate exactly when its tail dies. -/
theorem firstNodePositiveExtension_exact_iff (q : R[T;T⁻¹]) :
    leftLaurentMap (e) (firstNodePositiveExtension q (leftCoordinate (e))) =
      (firstOrderCoordinateUnit q).val ↔ boundaryTail q = 0 := by
  rw [firstNodePositiveExtension_leftLaurent, firstOrderCoordinateUnit_val,
    firstOrderLaurentCoordinate_injective.eq_iff, positivePart_toLaurent_iff]

/-- The remaining condition is a precise coefficient bound on the original field. -/
theorem firstNodePositiveExtension_exact_iff_coeff (q : R[T;T⁻¹]) :
    leftLaurentMap (e) (firstNodePositiveExtension q (leftCoordinate (e))) =
      (firstOrderCoordinateUnit q).val ↔ ∀ d : ℤ, d ≤ 0 → q.coeff d = 0 := by
  rw [firstNodePositiveExtension_exact_iff, boundaryTail_eq_zero_iff]

end FLT.Mazur.PolygonInfinitesimalStages

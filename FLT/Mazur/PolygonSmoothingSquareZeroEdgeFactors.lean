/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingSquareZeroShearBoundary
public import FLT.Mazur.LaurentSquareZeroBoundaryFactorization

/-!
# Whole-node factors of a square-zero edge correction

Every full Laurent correction splits into automorphisms of two adjacent
nodes. Both factors fix their opposite punctures. Their outgoing substitutions,
with the second conjugated by inversion, recover the original transition.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial LaurentBoundaryVectorField LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t e : R) (he : e ^ 2 = 0) (het : e * t = 0)
local notation "L" => R[T;T⁻¹]

/-- The positive Laurent part extends over the first full node. -/
def squareZeroPositiveFactor (q : L) : ChartRing t ≃ₐ[R] ChartRing t :=
  squareZeroShearEquiv t e he het (LaurentBoundaryCorrectionSplit.boundaryLift t (positivePart q))

/-- The complementary Laurent part extends over the other full node in reciprocal coordinate. -/
def squareZeroReciprocalFactor (q : L) : ChartRing t ≃ₐ[R] ChartRing t :=
  squareZeroShearEquiv t e he het
    (LaurentBoundaryCorrectionSplit.boundaryLift t (reciprocalField (nonpositivePart q)))

/-- The first factor recovers its entire outgoing substitution. -/
theorem squareZeroPositiveFactor_left (q : L) :
    (leftLaurentMap t).comp (squareZeroPositiveFactor t e he het q).toAlgHom =
      (LaurentSquareZeroAutomorphism.subst e he (positivePart q)).comp (leftLaurentMap t) := by
  change (leftLaurentMap t).comp (squareZeroShear t e het _) = _
  rw [squareZeroShear_leftLaurent t e he, positivePart_lift]

/-- The reciprocal factor also recovers its full outgoing substitution. -/
theorem squareZeroReciprocalFactor_left (q : L) :
    (leftLaurentMap t).comp (squareZeroReciprocalFactor t e he het q).toAlgHom =
      (LaurentSquareZeroAutomorphism.subst e he
        (reciprocalField (nonpositivePart q))).comp (leftLaurentMap t) := by
  change (leftLaurentMap t).comp (squareZeroShear t e het _) = _
  rw [squareZeroShear_leftLaurent t e he, nonpositivePart_reciprocal_lift]

/-- The first factor leaves its opposite full puncture unchanged. -/
theorem squareZeroPositiveFactor_right (q : L) :
    ((leftLaurentMap t).comp (branchSwapMap t)).comp
        (squareZeroPositiveFactor t e he het q).toAlgHom =
      (leftLaurentMap t).comp (branchSwapMap t) :=
  squareZeroShear_rightLaurent t e het _

/-- The second factor also leaves its opposite full puncture unchanged. -/
theorem squareZeroReciprocalFactor_right (q : L) :
    ((leftLaurentMap t).comp (branchSwapMap t)).comp
        (squareZeroReciprocalFactor t e he het q).toAlgHom =
      (leftLaurentMap t).comp (branchSwapMap t) :=
  squareZeroShear_rightLaurent t e het _

/-- The factored transition on the first node, using the full second boundary substitution. -/
theorem squareZeroEdgeFactorization (q : L) :
    (LaurentSquareZeroAutomorphism.subst e he q).comp (leftLaurentMap t) =
      (invert.toAlgHom.comp
        ((LaurentSquareZeroAutomorphism.subst e he
          (reciprocalField (nonpositivePart q))).comp invert.toAlgHom)).comp
            ((leftLaurentMap t).comp (squareZeroPositiveFactor t e he het q).toAlgHom) := by
  rw [squareZeroPositiveFactor_left, ← AlgHom.comp_assoc,
    LaurentSquareZeroAutomorphism.subst_reciprocal, reciprocalField_involutive,
    LaurentSquareZeroAutomorphism.subst_comp,
    show nonpositivePart q + positivePart q = q by rw [add_comm, parts_add]]

end FLT.Mazur.PolygonSmoothing

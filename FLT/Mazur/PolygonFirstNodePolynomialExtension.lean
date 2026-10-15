/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodePolynomialVectorField
public import FLT.Mazur.PolygonFirstNodeAutomorphism
public import FLT.Mazur.PolygonFirstNodeTangentBoundary

/-!
# Explicit node automorphisms extending polynomial branch fields

Polynomial vector fields vanishing at the branch origins construct actual
coordinate changes on xy = e. Their first Laurent restriction is precisely
the corresponding square-zero coordinate unit, over the full smoothing base.
These are constructions, not hypotheses supplying unknown endomorphisms.
-/

@[expose] public noncomputable section
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing NodePolynomialVectorField
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable {R : Type} [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "B" => ChartRing (e)

/-- Both polynomial fields construct a genuine automorphism of the original smoothing node. -/
def firstNodePolynomialExtension (p q : R[X])
    (hp : p.coeff 0 = 0) (hq : q.coeff 0 = 0) : (B) ≃ₐ[S] (B) :=
  firstNodeTangentAutomorphism R (derivation p q hp hq)

/-- The constructed extension reduces to the identity everywhere on the original node. -/
theorem firstNodePolynomialExtension_reduction (p q : R[X])
    (hp : p.coeff 0 = 0) (hq : q.coeff 0 = 0) (z : B) :
    firstNodeReduction R (firstNodePolynomialExtension p q hp hq z) =
      firstNodeReduction R z :=
  firstNodeTangentLift_reduction R (derivation p q hp hq) z

/-- The first branch restriction is the exact coordinate prescribed by the input polynomial. -/
theorem firstNodePolynomialExtension_leftLaurent (p q : R[X])
    (hp : p.coeff 0 = 0) (hq : q.coeff 0 = 0) :
    leftLaurentMap (e) (firstNodePolynomialExtension p q hp hq (leftCoordinate (e))) =
      firstOrderLaurentCoordinate p.toLaurent := by
  change leftLaurentMap (e)
    (firstNodeTangentLift R (derivation p q hp hq) (leftCoordinate (e))) = _
  rw [firstNodeTangentLift_leftLaurent, derivation_first]

/-- The original square-zero unit is actually extended, including every nilpotent coefficient. -/
theorem firstNodePolynomialExtension_coordinateUnit (p q : R[X])
    (hp : p.coeff 0 = 0) (hq : q.coeff 0 = 0) :
    leftLaurentMap (e) (firstNodePolynomialExtension p q hp hq (leftCoordinate (e))) =
      (firstOrderCoordinateUnit p.toLaurent).val := by
  rw [firstOrderCoordinateUnit_val, firstNodePolynomialExtension_leftLaurent]

/-- The entire inverse node coordinate change also reduces to the original identity. -/
theorem firstNodePolynomialExtension_symm_reduction (p q : R[X])
    (hp : p.coeff 0 = 0) (hq : q.coeff 0 = 0) (z : B) :
    firstNodeReduction R ((firstNodePolynomialExtension p q hp hq).symm z) =
      firstNodeReduction R z :=
  firstNodeEndomorphismEquiv_symm_reduction R _
    (firstNodeTangentLift_reduction R (derivation p q hp hq)) z

/-- The inverse is explicitly computed on every original function, not only Laurent points. -/
theorem firstNodePolynomialExtension_symm_apply (p q : R[X])
    (hp : p.coeff 0 = 0) (hq : q.coeff 0 = 0) (z : B) :
    (firstNodePolynomialExtension p q hp hq).symm z =
      z - (firstNodePolynomialExtension p q hp hq z - z) := rfl

end FLT.Mazur.PolygonInfinitesimalStages

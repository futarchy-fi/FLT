/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialRoot
public import FLT.Mazur.QuadraticIncidenceTranslation

/-!
# The full initial arithmetic equation in two-factor coordinates

Translation by a polynomial root is an isomorphism on the entire original
chart, including t=0. The original incidence parameter and scale are retained.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)

/-- The two-factor initial chart over the full original incidence line. -/
abbrev PolynomialSplitCoordinate :=
  AdjoinRoot (QuadraticIncidenceTranslation.splitPolynomial X (C s)
    (polynomialSlopeLinear W b3) r)

local notation "B" => PolynomialSplitCoordinate W s b3 r

/-- The translated slope in the full two-factor chart. -/
def polynomialSplitSlope : B :=
  AdjoinRoot.root (QuadraticIncidenceTranslation.splitPolynomial X (C s)
    (polynomialSlopeLinear W b3) r)

/-- The original incidence coordinate in the full two-factor chart. -/
def polynomialSplitIncidence : B := algebraMap R[X] B X

/-- The polynomial translation and its inverse identify the full original initial chart. -/
def polynomialSplitEquiv : Coordinate W s b3 b4 b6 ≃ₐ[R] B :=
  (QuadraticIncidenceTranslation.equiv X (C s) (polynomialSlopeLinear W b3)
    (polynomialSlopeConstant W b4 b6) r hr).restrictScalars R

/-- The equivalence retains the original incidence coordinate everywhere. -/
theorem polynomialSplitEquiv_t :
    polynomialSplitEquiv W s b3 b4 b6 r hr (t W s b3 b4 b6) =
      polynomialSplitIncidence W s b3 r :=
  (QuadraticIncidenceTranslation.forward X (C s) (polynomialSlopeLinear W b3)
    (polynomialSlopeConstant W b4 b6) r hr).commutes X

/-- The entire original slope is recovered by adding the constructed polynomial root. -/
theorem polynomialSplitEquiv_v :
    polynomialSplitEquiv W s b3 b4 b6 r hr (v W s b3 b4 b6) =
      polynomialSplitSlope W s b3 r + algebraMap R[X] B r :=
  QuadraticIncidenceTranslation.forward_root X (C s) (polynomialSlopeLinear W b3)
    (polynomialSlopeConstant W b4 b6) r hr

/-- The inverse retains t, including its zero locus. -/
theorem polynomialSplitEquiv_symm_t :
    (polynomialSplitEquiv W s b3 b4 b6 r hr).symm
      (polynomialSplitIncidence W s b3 r) = t W s b3 b4 b6 :=
  (QuadraticIncidenceTranslation.backward X (C s) (polynomialSlopeLinear W b3)
    (polynomialSlopeConstant W b4 b6) r hr).commutes X

/-- The inverse subtracts exactly the same polynomial root on all original functions. -/
theorem polynomialSplitEquiv_symm_v :
    (polynomialSplitEquiv W s b3 b4 b6 r hr).symm (polynomialSplitSlope W s b3 r) =
      v W s b3 b4 b6 - algebraMap R[X] (Coordinate W s b3 b4 b6) r :=
  QuadraticIncidenceTranslation.backward_root X (C s) (polynomialSlopeLinear W b3)
    (polynomialSlopeConstant W b4 b6) r hr

/-- The full translated chart retains the original smoothing scale. -/
theorem polynomialSplit_relation :
    polynomialSplitIncidence W s b3 r * (polynomialSplitSlope W s b3 r *
      (polynomialSplitSlope W s b3 r +
        algebraMap R[X] B (r + r + polynomialSlopeLinear W b3))) = algebraMap R B s := by
  rw [IsScalarTower.algebraMap_apply R R[X] B]
  exact QuadraticIncidenceTranslation.split_relation X (C s) (polynomialSlopeLinear W b3) r

end FLT.Mazur.WeierstrassModificationX

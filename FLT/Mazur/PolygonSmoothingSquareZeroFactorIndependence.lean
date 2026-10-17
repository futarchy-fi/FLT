/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LaurentBoundaryCorrectionScalar
public import FLT.Mazur.PolygonSmoothingSquareZeroTwoBranches

/-!
# Whole-node corrections do not depend on division choices

Only the parameter-weighted Laurent field determines each full-node factor.
The result includes both branches of the common terminal node, and does not
require cancellation of the square-zero scalar.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t e : R) (he : e ^ 2 = 0) (het : e * t = 0)
local notation "L" => R[T;T⁻¹]
local notation "E" => algebraMap R (ChartRing t) e

/-- Equality of weighted chart functions determines the entire shear and its inverse. -/
theorem squareZeroShearEquiv_congr {p q : ChartRing t} (h : E * p = E * q) :
    squareZeroShearEquiv t e he het p = squareZeroShearEquiv t e he het q := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply chartRing_hom_ext t
  · change squareZeroShear t e het p (leftCoordinate t) =
      squareZeroShear t e het q (leftCoordinate t)
    simp only [squareZeroShear_left]
    congr 1
    calc
      _ = leftCoordinate t * (E * p) := by ring
      _ = leftCoordinate t * (E * q) := congrArg (leftCoordinate t * ·) h
      _ = _ := by ring
  · change squareZeroShear t e het p (rightCoordinate t) =
      squareZeroShear t e het q (rightCoordinate t)
    simp only [squareZeroShear_right]

/-- The positive whole-node factor depends only on the weighted full residual. -/
theorem squareZeroPositiveFactor_congr {p q : L} (h : C e * p = C e * q) :
    squareZeroPositiveFactor t e he het p = squareZeroPositiveFactor t e he het q :=
  squareZeroShearEquiv_congr t e he het (positiveLift_weighted h t)

/-- The complementary whole-node factor has the same independence from division choices. -/
theorem squareZeroReciprocalFactor_congr {p q : L} (h : C e * p = C e * q) :
    squareZeroReciprocalFactor t e he het p = squareZeroReciprocalFactor t e he het q :=
  squareZeroShearEquiv_congr t e he het (reciprocalLift_weighted h t)

/-- Reflection preserves independence on the full second branch, not just its puncture. -/
theorem squareZeroReflectedFactor_congr {p q : L} (h : C e * p = C e * q) :
    squareZeroReflectedFactor t e he het p = squareZeroReflectedFactor t e he het q := by
  rw [squareZeroReflectedFactor_def, squareZeroReflectedFactor_def,
    squareZeroPositiveFactor_congr t e he het h]

/-- Both corrected branches on one whole node depend only on their weighted residuals. -/
theorem squareZeroTwoBranchFactor_congr {p q : Bool → L}
    (h : ∀ b, C e * p b = C e * q b) :
    squareZeroTwoBranchFactor t e he het p = squareZeroTwoBranchFactor t e he het q := by
  rw [squareZeroTwoBranchFactor_def, squareZeroTwoBranchFactor_def,
    squareZeroPositiveFactor_congr t e he het (h true),
    squareZeroReflectedFactor_congr t e he het (h false)]

/-- The entire Laurent automorphism depends only on its weighted coordinate correction. -/
theorem squareZeroLaurentEquiv_congr {p q : L} (h : C e * p = C e * q) :
    LaurentSquareZeroAutomorphism.equiv e he p = LaurentSquareZeroAutomorphism.equiv e he q := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply LaurentNilpotentReparametrization.hom_ext_positive
  change LaurentSquareZeroAutomorphism.equiv e he p (T 1) =
    LaurentSquareZeroAutomorphism.equiv e he q (T 1)
  simp only [LaurentSquareZeroAutomorphism.equiv_T, h]

/-- The full complementary overlap automorphism also ignores the choice of quotient. -/
theorem squareZeroReciprocalEquiv_congr {p q : L} (h : C e * p = C e * q) :
    LaurentSquareZeroAutomorphism.equiv e he
        (LaurentBoundaryVectorField.reciprocalField (nonpositivePart p)) =
      LaurentSquareZeroAutomorphism.equiv e he
        (LaurentBoundaryVectorField.reciprocalField (nonpositivePart q)) := by
  apply squareZeroLaurentEquiv_congr
  have hs : e • p = e • q := by simpa only [smul_eq_C_mul] using h
  have hh := congrArg (fun z ↦ LaurentBoundaryVectorField.reciprocalField (nonpositivePart z)) hs
  simp only [nonpositivePart_smul, reciprocalField_smul] at hh
  simpa only [smul_eq_C_mul] using hh

end FLT.Mazur.PolygonSmoothing

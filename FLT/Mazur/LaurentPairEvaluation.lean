/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentCoefficientEvaluation

/-!
# Evaluating the full double Laurent algebra at two units

The evaluation retains arbitrary coefficient algebras, including nonreduced
ones. It identifies the two projections and evaluates an arbitrary Laurent law.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentPairEvaluation
open LaurentPolynomial PolygonScalingNaturality LaurentUnitPoints
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- Substitute two actual units into the two Laurent coordinates. -/
def pairEval (u v : Bˣ) : R[T;T⁻¹][T;T⁻¹] →ₐ[R] B where
  __ := eval₂ (evalUnit (R := R) u).toRingHom v
  commutes' r := by
    change eval₂ (evalUnit (R := R) u).toRingHom v (C (C r)) = algebraMap R B r
    rw [eval₂_C]
    exact evalUnit_C _ _

/-- The first Laurent coordinate is evaluated at the first specified unit. -/
@[simp] theorem pairEval_C (u v : Bˣ) (p : R[T;T⁻¹]) :
    pairEval u v (C p) = evalUnit u p := eval₂_C _ _ _

/-- The second coordinate is evaluated at the second specified unit. -/
@[simp] theorem pairEval_T (u v : Bˣ) (d : ℤ) :
    pairEval (R := R) u v (T d) = (v ^ d).val := eval₂_T _ _ _

/-- Evaluating the inner coefficient inclusion recovers the first point. -/
theorem pairEval_first (u v : Bˣ) :
    (pairEval (R := R) u v).toRingHom.comp C = (evalUnit u).toRingHom :=
  RingHom.ext (pairEval_C u v)

/-- Evaluating the outer coefficient projection recovers the second point. -/
theorem pairEval_second (u v : Bˣ) :
    (pairEval (R := R) u v).toRingHom.comp (coeffMap (C : R →+* R[T;T⁻¹])) =
      (evalUnit v).toRingHom := by
  apply ringHom_ext
  · intro r
    simp
  · simp
  · simp

/-- Substituting into any Laurent law is evaluation at its resulting unit. -/
theorem pairEval_law (u v : Bˣ) (f : R[T;T⁻¹] →ₐ[R] R[T;T⁻¹][T;T⁻¹]) :
    (pairEval u v).comp f =
      evalUnit (Units.map (pairEval (R := R) u v).toMonoidHom (pointUnit f)) := by
  calc
    (pairEval u v).comp f = (pairEval u v).comp (evalUnit (pointUnit f)) :=
      congrArg ((pairEval u v).comp ·) (evalUnit_pointUnit f).symm
    _ = _ := evalUnit_natural (pairEval (R := R) u v) (pointUnit f)

end FLT.Mazur.LaurentPairEvaluation

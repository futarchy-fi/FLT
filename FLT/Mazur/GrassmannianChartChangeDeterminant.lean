/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSplitChartCoordinates
public import Mathlib.LinearAlgebra.Determinant

/-!
# Determinant criterion for a second quotient basis

On a split Grassmannian chart, any second selected summand maps bijectively to
its original quotient exactly when the change-of-basis determinant is a unit.
The criterion uses the entire quotient relation, over arbitrary commutative rings.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {S : Type*} [CommRing S] {V : Type*} [AddCommGroup V] [Module S V] {d : ℕ}

/-- Images of a second selected summand in normalized quotient coordinates. -/
def chartChangeMap (A : V →ₗ[S] (Fin d → S))
    (j : (Fin d → S) →ₗ[S] ((Fin d → S) × V)) :
    (Fin d → S) →ₗ[S] (Fin d → S) := (splitChartEvaluation A).comp j

/-- The determinant cutting out the second basis chart. -/
def chartChangeDet (A : V →ₗ[S] (Fin d → S))
    (j : (Fin d → S) →ₗ[S] ((Fin d → S) × V)) : S :=
  LinearMap.det (chartChangeMap A j)

/-- The determinant is also the determinant of the usual change-of-basis matrix. -/
theorem chartChangeDet_matrix (A : V →ₗ[S] (Fin d → S))
    (j : (Fin d → S) →ₗ[S] ((Fin d → S) × V)) :
    chartChangeDet A j = (LinearMap.toMatrix' (chartChangeMap A j)).det :=
  (LinearMap.det_toMatrix' _).symm

/-- Invertibility of the determinant is exactly bijectivity of the second basis map. -/
theorem chartChangeMap_bijective_iff (A : V →ₗ[S] (Fin d → S))
    (j : (Fin d → S) →ₗ[S] ((Fin d → S) × V)) :
    Function.Bijective (chartChangeMap A j) ↔ IsUnit (chartChangeDet A j) := by
  change Function.Bijective _ ↔ IsUnit (LinearMap.det _)
  rw [← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff]

/-- Actual membership in the second quotient chart is the principal determinant condition. -/
theorem splitChart_secondBasis_iff (N : SplitChart S V d)
    (j : (Fin d → S) →ₗ[S] ((Fin d → S) × V)) :
    Function.Bijective (N.val.toSubmodule.mkQ.comp j) ↔
      IsUnit (chartChangeDet (splitChartCoordinates N) j) := by
  rw [← chartChangeMap_bijective_iff]
  have h : N.val.toSubmodule.mkQ.comp j =
      (splitChartBasisEquiv N).toLinearMap.comp
        (chartChangeMap (splitChartCoordinates N) j) := by
    rw [chartChangeMap, ← LinearMap.comp_assoc, splitChartCoordinates_factor]
  rw [h]
  exact (splitChartBasisEquiv N).bijective.of_comp_iff' _

end FLT.Mazur.GrassmannianChart

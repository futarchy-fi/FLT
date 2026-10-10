/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCubicEquationTransition
public import Mathlib.Algebra.GroupWithZero.Regular

/-!
# Regularity of the cubic equations over a domain

The actual equation is nonzero in each homogeneous-localization chart.
Two charts have an evaluation equal to -1; the third retains a polynomial
with cubic coefficient -1. This includes every field fiber, even singular ones.
-/

@[expose] public noncomputable section

open MvPolynomial
open FLT.Mazur.ProjectiveSpace

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

/-- Every normalized evaluation of the ambient equation is the specified cubic. -/
theorem projectiveChartEquation_evaluation {S : Type} [CommRing S] [Algebra R S]
    (j : Fin 3) (v : Fin 3 → S) (hv : v j = 1) :
    chartEvaluation R S 2 (Equiv.swap 0 j) j (by simp) (algebraMap R S) v
      (projectiveChartEquation W j) = aeval v W.toProjective.polynomial := by
  rw [projectiveChartEquation, cubic_aeval, cubic_aeval]
  simp only [map_add, map_sub, map_mul, map_pow,
    chartEvaluation_coordinate R S 2 (Equiv.swap 0 j) j (by simp) _ _ hv]
  simp only [show algebraMap R (chartRing R (Fin 3) j) = chartScalars R (Fin 3) j from rfl,
    chartEvaluation_scalar]

/-- None of the genuine local cubic equations is zero over a nontrivial base. -/
theorem projectiveChartEquation_ne_zero [Nontrivial R] (j : Fin 3) :
    projectiveChartEquation W j ≠ 0 := by
  intro h
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at h
  · have he := projectiveChartEquation_evaluation W 0 (![1, 0, 0] : Fin 3 → R) rfl
    rw [h, map_zero, cubic_aeval] at he
    simp at he
  · have he := projectiveChartEquation_evaluation W 1 (![1, 1, 0] : Fin 3 → R) rfl
    rw [h, map_zero, cubic_aeval] at he
    simp at he
  · have he := projectiveChartEquation_evaluation W 2
      (![Polynomial.X, 0, 1] : Fin 3 → Polynomial R) rfl
    rw [h, map_zero, cubic_aeval] at he
    have hc := congrArg (fun p : Polynomial R => p.coeff 3) he
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C_mul] at hc

/-- Over every domain, each chart equation is a non-zero-divisor. -/
theorem projectiveChartEquation_regular [IsDomain R] (j : Fin 3) :
    IsRegular (projectiveChartEquation W j) := by
  let _ := Localization.Away.isDomain (MvPolynomial.X_ne_zero (R := R) j)
  let _ : IsDomain (chartRing R (Fin 3) j) :=
    Function.Injective.isDomain
      (algebraMap (chartRing R (Fin 3) j) (Localization.Away (X (R := R) j)))
      (HomogeneousLocalization.val_injective _)
  exact IsRegular.of_ne_zero (projectiveChartEquation_ne_zero W j)

end FLT.Mazur.WeierstrassIntegralChart

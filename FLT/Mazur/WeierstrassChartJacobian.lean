/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassNormalizedProjectivePoint
public import FLT.Mazur.WeierstrassProjectiveChartProduct

/-!
# Derivatives in the normalized cubic charts

Euler's identity eliminates the derivative in the normalized coordinate.
Consequently a nonsingular normalized field point has a nonzero derivative
in one of the two free coordinates. Derivative evaluation commutes with every
algebra map out of the actual integral chart ring.
-/

@[expose] public noncomputable section

open MvPolynomial WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The partial derivative of the homogeneous cubic, evaluated in its actual chart. -/
def chartPartial (W : WeierstrassCurve R) (j i : Fin 3) : Coordinate W j :=
  aeval (coord W j) (pderiv i W.toProjective.polynomial)

/-- Derivatives specialize to the derivatives of the coefficient-extended cubic. -/
theorem chartPartial_map (W : WeierstrassCurve R) (j i : Fin 3)
    (f : Coordinate W j →ₐ[R] S) :
    f (chartPartial W j i) = eval (f ∘ coord W j)
      (pderiv i (W.map (algebraMap R S)).toProjective.polynomial) := by
  rw [chartPartial, comp_aeval_apply, WeierstrassCurve.Projective.map_polynomial,
    pderiv_map, eval_map, ← aeval_def]
  rfl

/-- Euler's relation for the three actual chart derivatives. -/
theorem chartPartial_euler (W : WeierstrassCurve R) (j : Fin 3) :
    coord W j 0 * chartPartial W j 0 + coord W j 1 * chartPartial W j 1 +
      coord W j 2 * chartPartial W j 2 = 0 := by
  have h := (W.map (algebraMap R (Coordinate W j))).toProjective.polynomial_relation (coord W j)
  have he := coord_equation W j
  change eval (coord W j) _ = 0 at he
  rw [he, mul_zero] at h
  simpa only [polynomialX, polynomialY, polynomialZ,
    WeierstrassCurve.Projective.map_polynomial, pderiv_map, eval_map, ← aeval_def,
    chartPartial] using h.symm

/-- A normalized nonsingular field point has a nonzero derivative in a free coordinate. -/
theorem normalized_free_partial_exists {K : Type*} [Field K] (W : WeierstrassCurve K)
    (j : Fin 3) (v : Fin 3 → K) (hv : W.toProjective.Nonsingular v) (hj : v j = 1) :
    ∃ i : Fin 3, i ≠ j ∧ eval v (pderiv i W.toProjective.polynomial) ≠ 0 := by
  by_contra! h
  have he := W.toProjective.polynomial_relation v
  rw [hv.1, mul_zero] at he
  have hzero : ∀ i : Fin 3, eval v (pderiv i W.toProjective.polynomial) = 0 := by
    intro i
    by_cases hi : i = j
    · subst i
      fin_cases j
      · change v 0 = 1 at hj
        change eval v (pderiv (0 : Fin 3) W.toProjective.polynomial) = 0
        simpa only [polynomialX, polynomialY, polynomialZ, hj, h 1 (by decide),
          h 2 (by decide), mul_zero, add_zero, one_mul] using he.symm
      · change v 1 = 1 at hj
        change eval v (pderiv (1 : Fin 3) W.toProjective.polynomial) = 0
        simpa only [polynomialX, polynomialY, polynomialZ, hj, h 0 (by decide),
          h 2 (by decide), mul_zero, zero_add, add_zero, one_mul] using he.symm
      · change v 2 = 1 at hj
        change eval v (pderiv (2 : Fin 3) W.toProjective.polynomial) = 0
        simpa only [polynomialX, polynomialY, polynomialZ, hj, h 0 (by decide),
          h 1 (by decide), mul_zero, zero_add, one_mul] using he.symm
    · exact h i hi
  rcases hv.2 with hx | hy | hz
  · exact hx (hzero 0)
  · exact hy (hzero 1)
  · exact hz (hzero 2)

end FLT.Mazur.WeierstrassIntegralChart

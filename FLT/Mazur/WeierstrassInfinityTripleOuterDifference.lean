/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTriplePolynomials
public import FLT.Mazur.WeierstrassInfinityCubicDifference

/-!
# The explicit residual in the actual outer cubic comparison

The two outer cubics generally differ: their difference is their line separation
times a quadratic. The three common-center corrections equal exactly this
residual. This identity must not be mistaken for equality of the outer cubics
or for vanishing of the associativity minors.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The intercept of an actual input line, computed from its chosen left input. -/
def infinityTripleLineIntercept (j : Fin 4) : Γ(InfinityTripleFull W hΔ, ⊤) :=
  infinityTripleScalarZ W hΔ (infinityTripleLeftIndex j) -
    infinityTripleScalarSlope W hΔ j *
      infinityTripleScalarX W hΔ (infinityTripleLeftIndex j)

/-- The Z coordinate along one actual line in the polynomial algebra. -/
def infinityTripleLineZPolynomial (j : Fin 4) : Γ(InfinityTripleFull W hΔ, ⊤)[X] :=
  C (infinityTripleScalarSlope W hΔ j) * X + C (infinityTripleLineIntercept W hΔ j)

/-- The actual line cubic is the cubic evaluated along its explicit polynomial Z coordinate. -/
theorem infinityTripleLinePolynomial_eval (j : Fin 4) :
    let V := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    infinityTripleLinePolynomial W hΔ j =
      MvPolynomial.eval ![X, 1, infinityTripleLineZPolynomial W hΔ j]
        (V.map C).toProjective.polynomial := by
  simp only [infinityTripleLinePolynomial, infinitySpecializationLinePolynomial,
    infinityTripleLineZPolynomial, infinityTripleLineIntercept, infinityTripleScalarSlope,
    infinityTripleScalarX, infinityTripleScalarZ, infinityTripleScalarLaw_left_coord]
  rfl

/-- The difference of any two genuine line cubics factors by their line separation. -/
theorem infinityTripleLinePolynomial_sub (j k : Fin 4) :
    let V := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    infinityTripleLinePolynomial W hΔ j - infinityTripleLinePolynomial W hΔ k =
      (C (infinityTripleScalarSlope W hΔ j - infinityTripleScalarSlope W hΔ k) * X +
        C (infinityTripleLineIntercept W hΔ j - infinityTripleLineIntercept W hΔ k)) *
      infinitySlopeDenominator (V.map C) X
        (infinityTripleLineZPolynomial W hΔ j) (infinityTripleLineZPolynomial W hΔ k) := by
  dsimp only
  rw [infinityTripleLinePolynomial_eval, infinityTripleLinePolynomial_eval,
    infinityCubic_sub, infinityCubicDividedZ_one]
  congr 1
  simp only [infinityTripleLineZPolynomial, map_sub]
  ring

/-- The three common-center corrections equal the explicit outer line-separation residual. -/
theorem infinityTriplePencilPolynomial_outer_residual :
    let V := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    infinityTriplePointPolynomial W hΔ 2 * infinityTriplePencilPolynomial W hΔ 2 2 1 +
        infinityTriplePointPolynomial W hΔ 0 * infinityTriplePencilPolynomial W hΔ 0 0 3 -
        infinityTriplePointPolynomial W hΔ 1 * infinityTriplePencilPolynomial W hΔ 1 0 1 =
      (C (infinityTripleScalarSlope W hΔ 2 - infinityTripleScalarSlope W hΔ 3) * X +
        C (infinityTripleLineIntercept W hΔ 2 - infinityTripleLineIntercept W hΔ 3)) *
      infinitySlopeDenominator (V.map C) X
        (infinityTripleLineZPolynomial W hΔ 2) (infinityTripleLineZPolynomial W hΔ 3) := by
  rw [← infinityTripleLinePolynomial_outer_sub]
  exact infinityTripleLinePolynomial_sub W hΔ 2 3

end FLT.Mazur.WeierstrassIntegralChart

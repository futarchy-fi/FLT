/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleLineResidual
public import FLT.Mazur.WeierstrassInfinityLineParameter

/-!
# Exact cubic relations between the residual and the remaining minor

Substitute any actual negated point into any actual secant factorization.
Cubic subtraction expresses the discrepancy as its line residual times the
homogeneous divided Z-difference. No evaluated factor is assumed regular.
-/

@[expose] public noncomputable section

open AlgebraicGeometry WeierstrassCurve MvPolynomial

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- Every actual negated point is a zero of the homogeneous cubic. -/
theorem infinityTripleNegY_equation (i : Fin 7) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    eval ![infinityTripleScalarX W hΔ i, infinityTripleNegY W hΔ i,
      infinityTripleScalarZ W hΔ i] A.toProjective.polynomial = 0 := by
  dsimp only
  rw [infinityTripleNegY, infinityCubic_negate]
  exact infinityTripleScalar_equation W hΔ i

/-- An actual point's residual and minor satisfy the full secant cubic equation. -/
theorem infinityTripleNegLineResidual_cubic (i : Fin 7) (j : Fin 4) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let n := infinityTripleNegY W hΔ i
    let Z := infinityTripleScalarSlope W hΔ j * x i +
      infinityTripleLineIntercept W hΔ j * n
    infinityTripleScalarScale W hΔ j *
        (x i - x (infinityTripleLeftIndex j) * n) *
        (x i - x (infinityTripleRightIndex j) * n) *
        infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j) i +
      infinityTripleNegLineResidual W hΔ i j *
        infinityCubicDividedZ A (x i) n Z (z i) = 0 := by
  dsimp only
  have hc := infinityCubic_sub
    (W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤)))
    (infinityTripleScalarX W hΔ i) (infinityTripleNegY W hΔ i)
    (infinityTripleScalarSlope W hΔ j * infinityTripleScalarX W hΔ i +
      infinityTripleLineIntercept W hΔ j * infinityTripleNegY W hΔ i)
    (infinityTripleScalarZ W hΔ i)
  rw [infinityTripleNegY_equation] at hc
  have hf := infinityTripleScalar_factorization W hΔ j
    (infinityTripleScalarX W hΔ i) (infinityTripleNegY W hΔ i)
  change eval ![_, _, infinityTripleScalarSlope W hΔ j * infinityTripleScalarX W hΔ i +
      infinityTripleLineIntercept W hΔ j * infinityTripleNegY W hΔ i] _ = _ at hf
  rw [hf] at hc
  dsimp only [infinityTripleNegLineResidual, infinityTripleNegMinor, infinityTripleNegY]
  dsimp only [infinityTripleNegY] at hc
  linear_combination hc

/-- The associativity residual has an explicit cubic relation to the outer XY minor. -/
theorem infinityTriple_outer_residual_cubic :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let n := infinityTripleNegY W hΔ 6
    infinityTripleScalarScale W hΔ 2 * (x 6 - x 3 * n) * (x 6 - x 2 * n) *
        infinityTripleNegMinor W hΔ 5 6 +
      infinityTripleNegLineResidual W hΔ 6 2 *
        infinityCubicDividedZ A (x 6) n
          (infinityTripleScalarSlope W hΔ 2 * x 6 +
            infinityTripleLineIntercept W hΔ 2 * n) (z 6) = 0 :=
  infinityTripleNegLineResidual_cubic W hΔ 6 2

end FLT.Mazur.WeierstrassIntegralChart

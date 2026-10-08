/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityQuadraticLift
public import FLT.Mazur.WeierstrassInfinityTripleOuterPencils

/-!
# Homogeneous common-center comparisons on the full infinity member

Coefficient extraction homogenizes the polynomial pencil without dividing by Y.
The resulting identities can therefore be evaluated at negated points even
where their Y coordinates are not units.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

section Scalar

variable {S : Type*} [CommRing S] (W : WeierstrassCurve S)

/-- Homogenization preserves both third factors with no condition on the test coordinates. -/
theorem infinity_inner_pencil_homogeneous {x₁ x₂ x₃ z₁ z₂ z₃ l m u v u' v' c c' : S}
    (hl : l * (x₂ - x₁) = z₂ - z₁)
    (hm : m * (x₃ - x₂) = z₃ - z₂)
    (hcl : l * infinitySlopeDenominator W x₂ z₁ z₂ =
      infinitySlopeNumerator W x₁ x₂ z₁)
    (hcm : m * infinitySlopeDenominator W x₃ z₂ z₃ =
      infinitySlopeNumerator W x₂ x₃ z₂)
    (hx : u * c = infinityAdditionXYZ W x₁ x₂ z₁ l 0)
    (hn : (-1 - W.a₁ * u - W.a₃ * v) * c = infinityLineLeading W l)
    (hx' : u' * c' = infinityAdditionXYZ W x₂ x₃ z₂ m 0)
    (hn' : (-1 - W.a₁ * u' - W.a₃ * v') * c' = infinityLineLeading W m)
    (U V : S) :
    c * (U - x₁ * V) * ((-1 - W.a₁ * u - W.a₃ * v) * U - u * V) -
        c' * (U - x₃ * V) * ((-1 - W.a₁ * u' - W.a₃ * v') * U - u' * V) =
      (l - m) * infinityCubicDividedZ W U V
        (z₂ * V + l * (U - x₂ * V)) (z₂ * V + m * (U - x₂ * V)) := by
  have h := congrArg (fun p => infinityQuadraticLift p U V)
    (infinity_inner_pencil_polynomial_normalized W hl hm hcl hcm hx hn hx' hn')
  simpa only [mul_assoc, infinityQuadraticLift_sub, infinityQuadraticLift_C_mul,
    infinityQuadraticLift_factors, infinityQuadraticLift_denominator] using h

end Scalar

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The Q-centered comparison is valid at every homogeneous test coordinate. -/
theorem infinityTripleScalar_inner_pencil_homogeneous
    (U V : Γ(InfinityTripleFull W hΔ, ⊤)) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let l := infinityTripleScalarSlope W hΔ 0
    let m := infinityTripleScalarSlope W hΔ 1
    infinityTripleScalarScale W hΔ 0 * (U - x 0 * V) *
        ((-1 - A.a₁ * x 3 - A.a₃ * z 3) * U - x 3 * V) -
      infinityTripleScalarScale W hΔ 1 * (U - x 2 * V) *
        ((-1 - A.a₁ * x 4 - A.a₃ * z 4) * U - x 4 * V) =
      (l - m) * infinityCubicDividedZ A U V
        (z 1 * V + l * (U - x 1 * V)) (z 1 * V + m * (U - x 1 * V)) :=
  infinity_inner_pencil_homogeneous _
    (infinityTripleScalar_line W hΔ 0) (infinityTripleScalar_line W hΔ 1)
    (infinityTripleScalar_cubic W hΔ 0) (infinityTripleScalar_cubic W hΔ 1)
    (infinityTripleScalar_coord_mul W hΔ 0 0) (infinityTripleScalar_negY W hΔ 0)
    (infinityTripleScalar_coord_mul W hΔ 1 0) (infinityTripleScalar_negY W hΔ 1) U V

/-- The R-centered outer comparison also allows noninvertible test Y coordinates. -/
theorem infinityTripleScalar_left_outer_pencil_homogeneous
    (U V : Γ(InfinityTripleFull W hΔ, ⊤)) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let r := infinityTripleScalarSlope W hΔ 2
    let m := infinityTripleScalarSlope W hΔ 1
    infinityTripleScalarScale W hΔ 2 * (U - x 3 * V) *
        ((-1 - A.a₁ * x 5 - A.a₃ * z 5) * U - x 5 * V) -
      infinityTripleScalarScale W hΔ 1 * (U - x 1 * V) *
        ((-1 - A.a₁ * x 4 - A.a₃ * z 4) * U - x 4 * V) =
      (r - m) * infinityCubicDividedZ A U V
        (z 2 * V + r * (U - x 2 * V)) (z 2 * V + m * (U - x 2 * V)) :=
  infinity_inner_pencil_homogeneous _
    (infinityTripleScalar_line W hΔ 2) (infinityTripleScalar_line_swap W hΔ 1)
    (infinityTripleScalar_cubic W hΔ 2) (infinityTripleScalar_cubic_swap W hΔ 1)
    (infinityTripleScalar_coord_mul W hΔ 2 0) (infinityTripleScalar_negY W hΔ 2)
    (infinityTripleScalar_x_mul_swap W hΔ 1) (infinityTripleScalar_negY W hΔ 1) U V

/-- The P-centered outer comparison also allows noninvertible test Y coordinates. -/
theorem infinityTripleScalar_right_outer_pencil_homogeneous
    (U V : Γ(InfinityTripleFull W hΔ, ⊤)) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let l := infinityTripleScalarSlope W hΔ 0
    let s := infinityTripleScalarSlope W hΔ 3
    infinityTripleScalarScale W hΔ 0 * (U - x 1 * V) *
        ((-1 - A.a₁ * x 3 - A.a₃ * z 3) * U - x 3 * V) -
      infinityTripleScalarScale W hΔ 3 * (U - x 4 * V) *
        ((-1 - A.a₁ * x 6 - A.a₃ * z 6) * U - x 6 * V) =
      (l - s) * infinityCubicDividedZ A U V
        (z 0 * V + l * (U - x 0 * V)) (z 0 * V + s * (U - x 0 * V)) :=
  infinity_inner_pencil_homogeneous _
    (infinityTripleScalar_line_swap W hΔ 0) (infinityTripleScalar_line W hΔ 3)
    (infinityTripleScalar_cubic_swap W hΔ 0) (infinityTripleScalar_cubic W hΔ 3)
    (infinityTripleScalar_x_mul_swap W hΔ 0) (infinityTripleScalar_negY W hΔ 0)
    (infinityTripleScalar_coord_mul W hΔ 3 0) (infinityTripleScalar_negY W hΔ 3) U V

end FLT.Mazur.WeierstrassIntegralChart

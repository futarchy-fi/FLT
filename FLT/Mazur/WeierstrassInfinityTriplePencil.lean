/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleScalarCross
public import FLT.Mazur.WeierstrassInfinityReverseCross
public import FLT.Mazur.WeierstrassInfinityPencilPolynomial

/-!
# The actual inner pencil on the full infinity triple member

Both inner outputs enter one polynomial identity over the genuine section ring.
The complementary endpoint identity is obtained without changing the cover or
assuming that any input difference is regular.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The second actual inner output satisfies the reverse homogeneous cross relation. -/
theorem infinityTripleScalar_inner_cross_reverse :
    let V := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let l := infinityTripleScalarSlope W hΔ 0
    let m := infinityTripleScalarSlope W hΔ 1
    infinityTripleScalarScale W hΔ 1 * (x 2 - x 0) *
        ((-1 - V.a₁ * x 4 - V.a₃ * z 4) * x 0 - x 4) =
      (l - m) * infinitySlopeDenominator V (x 0) (z 1 + m * (x 0 - x 1)) (z 0) :=
  infinity_inner_cross_reverse_normalized _
    (infinityTripleScalar_line W hΔ 0) (infinityTripleScalar_line W hΔ 1)
    (infinityTripleScalar_cubic W hΔ 0) (infinityTripleScalar_cubic W hΔ 1)
    (infinityTripleScalar_coord_mul W hΔ 1 0) (infinityTripleScalar_negY W hΔ 1)

/-- A free scalar comparison simultaneously retains the two genuine inner output factors. -/
theorem infinityTripleScalar_inner_pencil (T : Γ(InfinityTripleFull W hΔ, ⊤)) :
    let V := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let l := infinityTripleScalarSlope W hΔ 0
    let m := infinityTripleScalarSlope W hΔ 1
    infinityTripleScalarScale W hΔ 0 * (T - x 0) *
        ((-1 - V.a₁ * x 3 - V.a₃ * z 3) * T - x 3) -
      infinityTripleScalarScale W hΔ 1 * (T - x 2) *
        ((-1 - V.a₁ * x 4 - V.a₃ * z 4) * T - x 4) =
      (l - m) * infinitySlopeDenominator V T
        (z 1 + l * (T - x 1)) (z 1 + m * (T - x 1)) :=
  infinity_inner_pencil_normalized _
    (infinityTripleScalar_line W hΔ 0) (infinityTripleScalar_line W hΔ 1)
    (infinityTripleScalar_cubic W hΔ 0) (infinityTripleScalar_cubic W hΔ 1)
    (infinityTripleScalar_coord_mul W hΔ 0 0) (infinityTripleScalar_negY W hΔ 0)
    (infinityTripleScalar_coord_mul W hΔ 1 0) (infinityTripleScalar_negY W hΔ 1) T

/-- The actual inner comparison is a polynomial identity, valid over nonreduced bases. -/
theorem infinityTripleScalar_inner_pencil_polynomial :
    let V := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let l := infinityTripleScalarSlope W hΔ 0
    let m := infinityTripleScalarSlope W hΔ 1
    C (infinityTripleScalarScale W hΔ 0) * (X - C (x 0)) *
        (C (-1 - V.a₁ * x 3 - V.a₃ * z 3) * X - C (x 3)) -
      C (infinityTripleScalarScale W hΔ 1) * (X - C (x 2)) *
        (C (-1 - V.a₁ * x 4 - V.a₃ * z 4) * X - C (x 4)) =
      C (l - m) * infinitySlopeDenominator (V.map C) X
        (C (z 1) + C l * (X - C (x 1))) (C (z 1) + C m * (X - C (x 1))) :=
  infinity_inner_pencil_polynomial_normalized _
    (infinityTripleScalar_line W hΔ 0) (infinityTripleScalar_line W hΔ 1)
    (infinityTripleScalar_cubic W hΔ 0) (infinityTripleScalar_cubic W hΔ 1)
    (infinityTripleScalar_coord_mul W hΔ 0 0) (infinityTripleScalar_negY W hΔ 0)
    (infinityTripleScalar_coord_mul W hΔ 1 0) (infinityTripleScalar_negY W hΔ 1)

end FLT.Mazur.WeierstrassIntegralChart

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTriplePencil

/-!
# Common-center polynomial comparisons involving the outer laws

At R compare (P+Q,R) with (R,Q); at P compare (Q,P) with (P,Q+R).
Together with the middle-input pencil, these identities contain all four actual
divided cubic equations on the genuine full-cover member.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The genuine scalar line relation may be read in the opposite direction. -/
theorem infinityTripleScalar_line_swap (j : Fin 4) :
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let a := infinityTripleLeftIndex j
    let b := infinityTripleRightIndex j
    infinityTripleScalarSlope W hΔ j * (x a - x b) = z a - z b := by
  dsimp only
  linear_combination -infinityTripleScalar_line W hΔ j

/-- Reversal preserves the tangent information in each actual divided cubic. -/
theorem infinityTripleScalar_cubic_swap (j : Fin 4) :
    let V := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let a := infinityTripleLeftIndex j
    let b := infinityTripleRightIndex j
    infinityTripleScalarSlope W hΔ j * infinitySlopeDenominator V (x a) (z b) (z a) =
      infinitySlopeNumerator V (x b) (x a) (z b) :=
  infinitySlope_cubic_swap _ (infinityTripleScalar_line W hΔ j)
    (infinityTripleScalar_cubic W hΔ j)

/-- The normalized output formula uses the same scale after input reversal. -/
theorem infinityTripleScalar_x_mul_swap (j : Fin 4) :
    let V := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let a := infinityTripleLeftIndex j
    let b := infinityTripleRightIndex j
    x (infinityTripleOutputIndex j) * infinityTripleScalarScale W hΔ j =
      infinityAdditionXYZ V (x b) (x a) (z b) (infinityTripleScalarSlope W hΔ j) 0 := by
  dsimp only
  rw [infinityAdditionXYZ_swap _ (infinityTripleScalar_line W hΔ j)]
  exact infinityTripleScalar_coord_mul W hΔ j 0

/-- The R-centered pencil compares the left outer output with the last inner output. -/
theorem infinityTripleScalar_left_outer_pencil :
    let V := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let r := infinityTripleScalarSlope W hΔ 2
    let m := infinityTripleScalarSlope W hΔ 1
    C (infinityTripleScalarScale W hΔ 2) * (X - C (x 3)) *
        (C (-1 - V.a₁ * x 5 - V.a₃ * z 5) * X - C (x 5)) -
      C (infinityTripleScalarScale W hΔ 1) * (X - C (x 1)) *
        (C (-1 - V.a₁ * x 4 - V.a₃ * z 4) * X - C (x 4)) =
      C (r - m) * infinitySlopeDenominator (V.map C) X
        (C (z 2) + C r * (X - C (x 2))) (C (z 2) + C m * (X - C (x 2))) :=
  infinity_inner_pencil_polynomial_normalized _
    (infinityTripleScalar_line W hΔ 2) (infinityTripleScalar_line_swap W hΔ 1)
    (infinityTripleScalar_cubic W hΔ 2) (infinityTripleScalar_cubic_swap W hΔ 1)
    (infinityTripleScalar_coord_mul W hΔ 2 0) (infinityTripleScalar_negY W hΔ 2)
    (infinityTripleScalar_x_mul_swap W hΔ 1) (infinityTripleScalar_negY W hΔ 1)

/-- The P-centered pencil compares the first inner output with the right outer output. -/
theorem infinityTripleScalar_right_outer_pencil :
    let V := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let l := infinityTripleScalarSlope W hΔ 0
    let s := infinityTripleScalarSlope W hΔ 3
    C (infinityTripleScalarScale W hΔ 0) * (X - C (x 1)) *
        (C (-1 - V.a₁ * x 3 - V.a₃ * z 3) * X - C (x 3)) -
      C (infinityTripleScalarScale W hΔ 3) * (X - C (x 4)) *
        (C (-1 - V.a₁ * x 6 - V.a₃ * z 6) * X - C (x 6)) =
      C (l - s) * infinitySlopeDenominator (V.map C) X
        (C (z 0) + C l * (X - C (x 0))) (C (z 0) + C s * (X - C (x 0))) :=
  infinity_inner_pencil_polynomial_normalized _
    (infinityTripleScalar_line_swap W hΔ 0) (infinityTripleScalar_line W hΔ 3)
    (infinityTripleScalar_cubic_swap W hΔ 0) (infinityTripleScalar_cubic W hΔ 3)
    (infinityTripleScalar_x_mul_swap W hΔ 0) (infinityTripleScalar_negY W hΔ 0)
    (infinityTripleScalar_coord_mul W hΔ 3 0) (infinityTripleScalar_negY W hΔ 3)

end FLT.Mazur.WeierstrassIntegralChart

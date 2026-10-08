/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleScalarLaws
public import FLT.Mazur.WeierstrassInfinityInnerCross

/-!
# Cubic splitting and the inner cross relation on the actual triple member

The homogeneous calculations now hold in the section ring of the genuine
all-infinity full-cover member. No extra affine-output condition is imposed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- Each of the seven actual points satisfies the Y-chart cubic. -/
theorem infinityTripleScalar_equation (i : Fin 7) :
    (W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))).toProjective.Equation
      ![infinityTripleScalarX W hΔ i, 1, infinityTripleScalarZ W hΔ i] := by
  have h := projective_equation_of_hom W 1 (infinityTripleScalarPoint W hΔ i)
  have he := Projective.fin3_def (infinityTripleScalarPoint W hΔ i ∘ coord W 1)
  simp only [Function.comp_apply, coord_self, map_one] at he
  rw [← he] at h
  exact h

/-- Every normalized negated output lies on its actual input line. -/
theorem infinityTripleScalar_output_line (j : Fin 4) :
    let V := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let m := infinityTripleScalarSlope W hΔ j
    let a := infinityTripleLeftIndex j
    let k := infinityTripleOutputIndex j
    let b := z a - m * x a
    (1 + V.a₃ * b) * z k + (V.a₁ * b - m) * x k + b = 0 := by
  simpa only [infinityTripleScalarX, infinityTripleScalarZ, infinityTripleScalarSlope,
    infinityTripleScalarLaw_left_coord, infinityTripleScalarLaw_output_coord] using
    infinitySpecialization_output_line W (infinityTripleScalarLaw W hΔ j)

/-- The four actual line cubics split, with only the genuine output unit as a prefactor. -/
theorem infinityTripleScalar_factorization (j : Fin 4)
    (X Y : Γ(InfinityTripleFull W hΔ, ⊤)) :
    let V := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let m := infinityTripleScalarSlope W hΔ j
    let a := infinityTripleLeftIndex j
    let b := infinityTripleRightIndex j
    let k := infinityTripleOutputIndex j
    MvPolynomial.eval ![X, Y, m * X + (z a - m * x a) * Y] V.toProjective.polynomial =
      infinityTripleScalarScale W hΔ j * (X - x a * Y) * (X - x b * Y) *
        ((-1 - V.a₁ * x k - V.a₃ * z k) * X - x k * Y) := by
  simpa only [infinityTripleScalarX, infinityTripleScalarZ, infinityTripleScalarSlope,
    infinityTripleScalarScale, infinityTripleScalarLaw_left_coord,
    infinityTripleScalarLaw_right_coord, infinityTripleScalarLaw_output_coord] using
    infinitySpecialization_factorization W (infinityTripleScalarLaw W hΔ j) X Y

/-- The first inner sum and the last inner slope satisfy the homogeneous cross relation. -/
theorem infinityTripleScalar_inner_cross :
    let V := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let l := infinityTripleScalarSlope W hΔ 0
    let m := infinityTripleScalarSlope W hΔ 1
    infinityTripleScalarScale W hΔ 0 * (x 2 - x 0) *
        ((-1 - V.a₁ * x 3 - V.a₃ * z 3) * x 2 - x 3) =
      (l - m) * infinitySlopeDenominator V (x 2) (z 1 + l * (x 2 - x 1)) (z 2) :=
  infinity_inner_cross_normalized _
    (infinityTripleScalar_line W hΔ 0) (infinityTripleScalar_line W hΔ 1)
    (infinityTripleScalar_cubic W hΔ 0) (infinityTripleScalar_cubic W hΔ 1)
    (infinityTripleScalar_coord_mul W hΔ 0 0) (infinityTripleScalar_negY W hΔ 0)

/-- The last linear factor is unimodular even where its leading coefficient is not a unit. -/
theorem infinityTripleScalar_third_unimodular (j : Fin 4) :
    let V := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let m := infinityTripleScalarSlope W hΔ j
    let a := infinityTripleLeftIndex j
    let k := infinityTripleOutputIndex j
    let b := z a - m * x a
    (-1 - V.a₁ * x k - V.a₃ * z k) * (-(1 + V.a₃ * b)) +
      x k * (-(V.a₁ + V.a₃ * m)) = 1 := by
  simpa only [infinityTripleScalarX, infinityTripleScalarZ, infinityTripleScalarSlope,
    infinityTripleScalarLaw_left_coord, infinityTripleScalarLaw_output_coord] using
    infinitySpecialization_third_unimodular W (infinityTripleScalarLaw W hΔ j)

end FLT.Mazur.WeierstrassIntegralChart

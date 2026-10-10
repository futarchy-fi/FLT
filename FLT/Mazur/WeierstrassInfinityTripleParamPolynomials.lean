/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityQuadraticBaseChange
public import FLT.Mazur.WeierstrassInfinityTripleOutputParameter

/-!
# Common centered parameters in the actual section polynomial ring

Every pencil uses the same determinant-one change of variables. Coefficient
extension is performed before substitution, so the equations hold as polynomials
also over finite and nonreduced section rings.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The old X coordinate, centered at the output of law `j`. -/
def infinityTripleParamXPolynomial (j : Fin 4) : Γ(InfinityTripleFull W hΔ, ⊤)[X] :=
  let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
  (-C (1 + A.a₃ * infinityTripleLineIntercept W hΔ j)) * X +
    C (infinityTripleScalarX W hΔ (infinityTripleOutputIndex j))

/-- The old homogeneous Y coordinate in the same polynomial parameters. -/
def infinityTripleParamYPolynomial (j : Fin 4) : Γ(InfinityTripleFull W hΔ, ⊤)[X] :=
  let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
  C (A.a₁ + A.a₃ * infinityTripleScalarSlope W hΔ j) * X +
    C (infinityTripleNegY W hΔ (infinityTripleOutputIndex j))

/-- An actual input factor after the common parameter change. -/
def infinityTripleParamInputPolynomial (j : Fin 4) (i : Fin 7) :
    Γ(InfinityTripleFull W hΔ, ⊤)[X] :=
  infinityTripleParamXPolynomial W hΔ j -
    C (infinityTripleScalarX W hΔ i) * infinityTripleParamYPolynomial W hΔ j

/-- An actual homogeneous third factor after the common parameter change. -/
def infinityTripleParamThirdPolynomial (j : Fin 4) (i : Fin 7) :
    Γ(InfinityTripleFull W hΔ, ⊤)[X] :=
  C (infinityTripleNegY W hΔ i) * infinityTripleParamXPolynomial W hΔ j -
    C (infinityTripleScalarX W hΔ i) * infinityTripleParamYPolynomial W hΔ j

/-- Transport a genuine quadratic pencil into parameters centered at law `j`. -/
def infinityTripleParamPencilPolynomial (j : Fin 4) (i : Fin 7) (k l : Fin 4) :
    Γ(InfinityTripleFull W hΔ, ⊤)[X] :=
  infinityQuadraticBaseChange C (infinityTriplePencilPolynomial W hΔ i k l)
    (infinityTripleParamXPolynomial W hΔ j) (infinityTripleParamYPolynomial W hΔ j)

/-- The transformed pencil retains its explicit divided cubic correction. -/
theorem infinityTripleParamPencilPolynomial_eq (j : Fin 4) (i : Fin 7) (k l : Fin 4) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let U := infinityTripleParamXPolynomial W hΔ j
    let V := infinityTripleParamYPolynomial W hΔ j
    let E := infinityTripleParamInputPolynomial W hΔ j i
    let Z := C (infinityTripleScalarZ W hΔ i) * V
    infinityTripleParamPencilPolynomial W hΔ j i k l =
      C (infinityTripleScalarSlope W hΔ k - infinityTripleScalarSlope W hΔ l) *
        infinityCubicDividedZ (A.map C) U V
          (Z + C (infinityTripleScalarSlope W hΔ k) * E)
          (Z + C (infinityTripleScalarSlope W hΔ l) * E) := by
  simp only [infinityTripleParamPencilPolynomial, infinityTriplePencilPolynomial,
    infinityTripleParamInputPolynomial, infinityQuadraticBaseChange_C_mul,
    infinityQuadraticBaseChange_denominator]

/-- The centered law's own third factor is the free polynomial variable. -/
theorem infinityTripleParamThirdPolynomial_self (j : Fin 4) :
    infinityTripleParamThirdPolynomial W hΔ j (infinityTripleOutputIndex j) = X := by
  have h := congrArg (C : Γ(InfinityTripleFull W hΔ, ⊤) →+*
    Γ(InfinityTripleFull W hΔ, ⊤)[X])
      (infinity_negated_line_determinant _ (infinityTripleNegLineResidual_output W hΔ j))
  simp only [map_sub, map_add, map_neg, map_one, map_mul] at h
  unfold infinityTripleParamThirdPolynomial infinityTripleParamXPolynomial
    infinityTripleParamYPolynomial infinityTripleNegY
  simp only [map_sub, map_add, map_neg, map_one, map_mul]
  linear_combination X * h

/-- The inner pencil is an identity in common polynomial parameters. -/
theorem infinityTripleParamPencilPolynomial_inner (j : Fin 4) :
    C (infinityTripleScalarScale W hΔ 0) * infinityTripleParamInputPolynomial W hΔ j 0 *
        infinityTripleParamThirdPolynomial W hΔ j 3 -
      C (infinityTripleScalarScale W hΔ 1) * infinityTripleParamInputPolynomial W hΔ j 2 *
        infinityTripleParamThirdPolynomial W hΔ j 4 =
      infinityTripleParamPencilPolynomial W hΔ j 1 0 1 := by
  have h := congrArg (fun p => infinityQuadraticBaseChange C p
    (infinityTripleParamXPolynomial W hΔ j) (infinityTripleParamYPolynomial W hΔ j))
      (infinityTriplePencilPolynomial_inner W hΔ)
  simpa only [infinityTriplePointPolynomial, infinityTripleThirdPolynomial,
    infinityTripleParamInputPolynomial, infinityTripleParamThirdPolynomial,
    infinityTripleParamPencilPolynomial, infinityTripleNegY, mul_assoc,
    infinityQuadraticBaseChange_sub, infinityQuadraticBaseChange_C_mul,
    infinityQuadraticBaseChange_factors] using h

/-- The left pencil is an identity in common polynomial parameters. -/
theorem infinityTripleParamPencilPolynomial_left (j : Fin 4) :
    C (infinityTripleScalarScale W hΔ 2) * infinityTripleParamInputPolynomial W hΔ j 3 *
        infinityTripleParamThirdPolynomial W hΔ j 5 -
      C (infinityTripleScalarScale W hΔ 1) * infinityTripleParamInputPolynomial W hΔ j 1 *
        infinityTripleParamThirdPolynomial W hΔ j 4 =
      infinityTripleParamPencilPolynomial W hΔ j 2 2 1 := by
  have h := congrArg (fun p => infinityQuadraticBaseChange C p
    (infinityTripleParamXPolynomial W hΔ j) (infinityTripleParamYPolynomial W hΔ j))
      (infinityTriplePencilPolynomial_left W hΔ)
  simpa only [infinityTriplePointPolynomial, infinityTripleThirdPolynomial,
    infinityTripleParamInputPolynomial, infinityTripleParamThirdPolynomial,
    infinityTripleParamPencilPolynomial, infinityTripleNegY, mul_assoc,
    infinityQuadraticBaseChange_sub, infinityQuadraticBaseChange_C_mul,
    infinityQuadraticBaseChange_factors] using h

/-- The right pencil is an identity in common polynomial parameters. -/
theorem infinityTripleParamPencilPolynomial_right (j : Fin 4) :
    C (infinityTripleScalarScale W hΔ 0) * infinityTripleParamInputPolynomial W hΔ j 1 *
        infinityTripleParamThirdPolynomial W hΔ j 3 -
      C (infinityTripleScalarScale W hΔ 3) * infinityTripleParamInputPolynomial W hΔ j 4 *
        infinityTripleParamThirdPolynomial W hΔ j 6 =
      infinityTripleParamPencilPolynomial W hΔ j 0 0 3 := by
  have h := congrArg (fun p => infinityQuadraticBaseChange C p
    (infinityTripleParamXPolynomial W hΔ j) (infinityTripleParamYPolynomial W hΔ j))
      (infinityTriplePencilPolynomial_right W hΔ)
  simpa only [infinityTriplePointPolynomial, infinityTripleThirdPolynomial,
    infinityTripleParamInputPolynomial, infinityTripleParamThirdPolynomial,
    infinityTripleParamPencilPolynomial, infinityTripleNegY, mul_assoc,
    infinityQuadraticBaseChange_sub, infinityQuadraticBaseChange_C_mul,
    infinityQuadraticBaseChange_factors] using h

end FLT.Mazur.WeierstrassIntegralChart

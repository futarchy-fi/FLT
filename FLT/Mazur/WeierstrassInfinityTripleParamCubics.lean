/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleParamRegular

/-!
# Actual line cubics in one common polynomial parameter system

All four cubics factor using their genuine unit normalizers and actual input and
output factors. The common parameter system permits polynomial cancellation
and compares the outer cubics with their full line-separation residual retained.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The Z coordinate of law `k` in parameters centered at law `j`. -/
def infinityTripleParamLineZPolynomial (j k : Fin 4) : Γ(InfinityTripleFull W hΔ, ⊤)[X] :=
  C (infinityTripleScalarSlope W hΔ k) * infinityTripleParamXPolynomial W hΔ j +
    C (infinityTripleLineIntercept W hΔ k) * infinityTripleParamYPolynomial W hΔ j

/-- The actual cubic restricted to a line in the common polynomial parameters. -/
def infinityTripleParamLinePolynomial (j k : Fin 4) : Γ(InfinityTripleFull W hΔ, ⊤)[X] :=
  MvPolynomial.eval ![infinityTripleParamXPolynomial W hΔ j,
    infinityTripleParamYPolynomial W hΔ j, infinityTripleParamLineZPolynomial W hΔ j k]
    (W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤)[X])).toProjective.polynomial

/-- All four genuine line cubics split into their actual factors in the same parameter system. -/
theorem infinityTripleParamLinePolynomial_eq (j k : Fin 4) :
    infinityTripleParamLinePolynomial W hΔ j k =
      C (infinityTripleScalarScale W hΔ k) *
        infinityTripleParamInputPolynomial W hΔ j (infinityTripleLeftIndex k) *
        infinityTripleParamInputPolynomial W hΔ j (infinityTripleRightIndex k) *
        infinityTripleParamThirdPolynomial W hΔ j (infinityTripleOutputIndex k) := by
  have h := infinitySpecialization_factorization W
    ((CAlgHom (R := R)).comp (infinityTripleScalarLaw W hΔ k))
      (infinityTripleParamXPolynomial W hΔ j) (infinityTripleParamYPolynomial W hΔ j)
  simpa only [infinityTripleParamLinePolynomial, infinityTripleParamLineZPolynomial,
    infinityTripleParamInputPolynomial, infinityTripleParamThirdPolynomial,
    infinityTripleNegY, infinityTripleScalarScale, infinityTripleScalarX,
    infinityTripleScalarZ, infinityTripleScalarSlope, infinityTripleLineIntercept,
    infinityTripleScalarLaw_left_coord, infinityTripleScalarLaw_right_coord,
    infinityTripleScalarLaw_output_coord, AlgHom.comp_apply, CAlgHom_apply,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, Polynomial.algebraMap_apply,
    map_sub, map_add, map_neg, map_one, map_mul] using h

/-- The cubic belonging to the chosen center has third factor X. -/
theorem infinityTripleParamLinePolynomial_self (j : Fin 4) :
    infinityTripleParamLinePolynomial W hΔ j j =
      C (infinityTripleScalarScale W hΔ j) *
        infinityTripleParamInputPolynomial W hΔ j (infinityTripleLeftIndex j) *
        infinityTripleParamInputPolynomial W hΔ j (infinityTripleRightIndex j) * X := by
  rw [infinityTripleParamLinePolynomial_eq, infinityTripleParamThirdPolynomial_self]

/-- Every line cubic is regular in any of the common parameter systems. -/
theorem infinityTripleParamLinePolynomial_regular (j k : Fin 4) :
    IsRegular (infinityTripleParamLinePolynomial W hΔ j k) := by
  rw [infinityTripleParamLinePolynomial_eq]
  exact ((((infinityTripleScalar_scale_unit W hΔ k).map C).isRegular.mul
    (infinityTripleParamInputPolynomial_regular W hΔ j _)).mul
      (infinityTripleParamInputPolynomial_regular W hΔ j _)).mul
        (infinityTripleParamThirdPolynomial_regular W hΔ j k)

/-- Polynomial cancellation by an entire actual cubic is valid before specialization. -/
theorem infinityTripleParamLinePolynomial_cancel (j k : Fin 4)
    (p q : Γ(InfinityTripleFull W hΔ, ⊤)[X]) :
    infinityTripleParamLinePolynomial W hΔ j k * p =
      infinityTripleParamLinePolynomial W hΔ j k * q ↔ p = q :=
  (infinityTripleParamLinePolynomial_regular W hΔ j k).left.eq_iff

/-- The outer cubic comparison retains the three transported corrections exactly. -/
theorem infinityTripleParamLinePolynomial_outer (j : Fin 4) :
    infinityTripleParamLinePolynomial W hΔ j 2 -
        infinityTripleParamLinePolynomial W hΔ j 3 =
      infinityTripleParamInputPolynomial W hΔ j 2 *
          infinityTripleParamPencilPolynomial W hΔ j 2 2 1 +
        infinityTripleParamInputPolynomial W hΔ j 0 *
          infinityTripleParamPencilPolynomial W hΔ j 0 0 3 -
        infinityTripleParamInputPolynomial W hΔ j 1 *
          infinityTripleParamPencilPolynomial W hΔ j 1 0 1 := by
  rw [infinityTripleParamLinePolynomial_eq, infinityTripleParamLinePolynomial_eq]
  change C (infinityTripleScalarScale W hΔ 2) *
      infinityTripleParamInputPolynomial W hΔ j 3 *
      infinityTripleParamInputPolynomial W hΔ j 2 *
      infinityTripleParamThirdPolynomial W hΔ j 5 -
    C (infinityTripleScalarScale W hΔ 3) *
      infinityTripleParamInputPolynomial W hΔ j 0 *
      infinityTripleParamInputPolynomial W hΔ j 4 *
      infinityTripleParamThirdPolynomial W hΔ j 6 = _
  linear_combination
    infinityTripleParamInputPolynomial W hΔ j 2 *
      infinityTripleParamPencilPolynomial_left W hΔ j +
    infinityTripleParamInputPolynomial W hΔ j 0 *
      infinityTripleParamPencilPolynomial_right W hΔ j -
    infinityTripleParamInputPolynomial W hΔ j 1 *
      infinityTripleParamPencilPolynomial_inner W hΔ j

/-- The difference of outer cubics is the actual line separation times the divided cubic. -/
theorem infinityTripleParamLinePolynomial_sub (j k l : Fin 4) :
    infinityTripleParamLinePolynomial W hΔ j k -
        infinityTripleParamLinePolynomial W hΔ j l =
      (infinityTripleParamLineZPolynomial W hΔ j k -
        infinityTripleParamLineZPolynomial W hΔ j l) *
      infinityCubicDividedZ (W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤)[X]))
        (infinityTripleParamXPolynomial W hΔ j) (infinityTripleParamYPolynomial W hΔ j)
        (infinityTripleParamLineZPolynomial W hΔ j k)
        (infinityTripleParamLineZPolynomial W hΔ j l) :=
  infinityCubic_sub _ _ _ _ _

end FLT.Mazur.WeierstrassIntegralChart

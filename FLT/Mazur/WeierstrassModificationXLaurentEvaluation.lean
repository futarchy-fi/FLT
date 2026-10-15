/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLaurentRoot

/-!
# The original initial chart evaluated at a Laurent slope

A solution of the original initial quadratic gives a map on every original
function and on the whole incidence localization, retaining its scale.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[T;T⁻¹]) (hr : r ^ 2 + laurentSlopeLinear W b3 * r =
    laurentSlopeConstant W s b4 b6)

include hr in
/-- The original initial incidence equation holds on the whole Laurent branch. -/
theorem laurentSlope_incidence :
    LaurentPolynomial.T (-1) *
      (r ^ 2 + (algebraMap R R[T;T⁻¹] W.a₁ +
        algebraMap R R[T;T⁻¹] b3 * LaurentPolynomial.T (-1)) * r -
        (algebraMap R R[T;T⁻¹] W.a₂ +
          algebraMap R R[T;T⁻¹] b4 * LaurentPolynomial.T (-1) +
            algebraMap R R[T;T⁻¹] b6 * LaurentPolynomial.T (-1) ^ 2)) =
      algebraMap R R[T;T⁻¹] s := by
  change LaurentPolynomial.T (-1) * (r ^ 2 + laurentSlopeLinear W b3 * r - _) = _
  rw [hr]
  change LaurentPolynomial.T (-1) *
    (LaurentPolynomial.C s * LaurentPolynomial.T 1 + LaurentPolynomial.C W.a₂ +
      LaurentPolynomial.C b4 * LaurentPolynomial.T (-1) +
        LaurentPolynomial.C b6 * LaurentPolynomial.T (-1) ^ 2 -
      (LaurentPolynomial.C W.a₂ + LaurentPolynomial.C b4 * LaurentPolynomial.T (-1) +
        LaurentPolynomial.C b6 * LaurentPolynomial.T (-1) ^ 2)) = LaurentPolynomial.C s
  calc _ = LaurentPolynomial.C s *
        (LaurentPolynomial.T (-1) * LaurentPolynomial.T 1) := by ring
    _ = _ := by rw [← LaurentPolynomial.T_add]; simp

/-- The actual original initial coordinate algebra evaluated at its full Laurent slope. -/
def laurentSlopeEvaluation : Coordinate W s b3 b4 b6 →ₐ[R] R[T;T⁻¹] :=
  evaluation W s b3 b4 b6 (LaurentPolynomial.T (-1)) r
    (laurentSlope_incidence W s b3 b4 b6 r hr)

/-- The original initial incidence is the inverse Laurent coordinate. -/
@[simp] theorem laurentSlopeEvaluation_t :
    laurentSlopeEvaluation W s b3 b4 b6 r hr (t W s b3 b4 b6) =
      LaurentPolynomial.T (-1) := evaluation_t ..

/-- The original initial slope is the selected full Laurent solution. -/
@[simp] theorem laurentSlopeEvaluation_v :
    laurentSlopeEvaluation W s b3 b4 b6 r hr (v W s b3 b4 b6) = r := evaluation_v ..

/-- The complete original initial incidence localization has the same Laurent evaluation. -/
def laurentSlopeLocalization : XOpen W s b3 b4 b6 →ₐ[R] R[T;T⁻¹] :=
  IsLocalization.Away.liftAlgHom (t W s b3 b4 b6)
    (f := laurentSlopeEvaluation W s b3 b4 b6 r hr)
    (by rw [laurentSlopeEvaluation_t]; exact LaurentPolynomial.isUnit_T (-1))

/-- Localization retains every original initial function. -/
theorem laurentSlopeLocalization_base (z : Coordinate W s b3 b4 b6) :
    laurentSlopeLocalization W s b3 b4 b6 r hr (algebraMap _ _ z) =
      laurentSlopeEvaluation W s b3 b4 b6 r hr z := by
  rw [laurentSlopeLocalization, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

end FLT.Mazur.WeierstrassModificationX

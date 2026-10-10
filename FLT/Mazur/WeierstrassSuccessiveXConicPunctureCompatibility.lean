/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXConicPuncturedParameters

/-!
# The punctured maps restrict the original ordered conic parameters

The explicit Laurent evaluations are the restrictions of the two established
rational parameter charts. Thus their coordinate and sign choices preserve
the original markings instead of choosing a new parameterization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory LaurentPolynomial
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (c : R) (hc : c = 0)

/-- Restrict the original zero-constant parameter line to its Laurent puncture. -/
def conicZeroPuncture : ConicParameterOpen c →ₐ[R] R[T;T⁻¹] :=
  IsLocalization.Away.liftAlgHom (f := Polynomial.toLaurentAlg)
    (conicParameterPolynomial c) (by
      rw [hc]
      simp only [conicParameterPolynomial, map_zero, zero_mul, sub_zero, map_one, isUnit_one])

/-- The puncture retains every polynomial function of the original parameter. -/
theorem conicZeroPuncture_base (p : R[X]) :
    conicZeroPuncture c hc (algebraMap R[X] (ConicParameterOpen c) p) =
      Polynomial.toLaurent p := by
  rw [conicZeroPuncture, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- The original parameter becomes the Laurent generator. -/
theorem conicZeroPuncture_z : conicZeroPuncture c hc (conicParameterZ c) = T 1 := by
  rw [conicParameterZ, conicZeroPuncture_base, Polynomial.toLaurent_X]

include hc in
/-- The zero-constant chart denominator has inverse one on the whole parameter line. -/
theorem conicParameterInv_of_zero : conicParameterInv c = 1 := by
  subst c
  simpa only [map_zero, zero_mul, sub_zero, one_mul] using conicParameter_mul_inv (0 : R)

/-- Restriction keeps the first original incidence formula. -/
theorem conicZeroPuncture_inverseT (a : R) :
    conicZeroPuncture c hc (conicInverseT a c) = C a * T 1 := by
  rw [conicInverseT, conicParameterInv_of_zero c hc, mul_one, map_mul,
    AlgHom.commutes, conicZeroPuncture_z]
  rfl

include hc in
/-- The original inverse slope vanishes when the conic constant does. -/
theorem conicInverseV_of_zero (a : R) : conicInverseV a c = 0 := by
  rw [conicInverseV, hc, map_zero, mul_zero, zero_mul, zero_mul]

variable (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
local notation "C₀" => ConicCoordinate W.a₁ c
local notation "O₁" => ConicFirstOpen W.a₁ c
local notation "O₂" => ConicSecondOpen W.a₁ c

/-- The first explicit puncture is the restriction of the original first parameter chart. -/
theorem conicPuncturedFirst_parameter : conicPuncturedFirst W c hc =
    (conicZeroPuncture c hc).comp
      ((conicFirstParameterEquiv W.a₁ c ha).symm.toAlgHom.comp (Algebra.algHom R C₀ O₁)) := by
  apply conic_hom_ext W.a₁ c
  · change conicEvaluation _ _ _ _ _ (conicT _ _) =
      conicZeroPuncture c hc
        (conicFirstToParameter W.a₁ c ha (algebraMap C₀ O₁ (conicT W.a₁ c)))
    rw [conicEvaluation_t, conicFirstToParameter_base, conicToParameter_t,
      conicZeroPuncture_inverseT]
  · change conicEvaluation _ _ _ _ _ (conicV _ _) =
      conicZeroPuncture c hc
        (conicFirstToParameter W.a₁ c ha (algebraMap C₀ O₁ (conicV W.a₁ c)))
    rw [conicEvaluation_v, conicFirstToParameter_base, conicToParameter_v,
      conicInverseV_of_zero c hc, map_zero]

/-- The second explicit puncture restricts the original second chart, including its sign. -/
theorem conicPuncturedSecond_parameter : conicPuncturedSecond W c hc =
    (conicZeroPuncture c hc).comp
      ((conicSecondParameterEquiv W.a₁ c ha).symm.toAlgHom.comp (Algebra.algHom R C₀ O₂)) := by
  apply conic_hom_ext W.a₁ c
  · change conicEvaluation _ _ _ _ _ (conicT _ _) = conicZeroPuncture c hc
      ((conicSecondParameterEquiv W.a₁ c ha).symm (algebraMap C₀ O₂ (conicT W.a₁ c)))
    rw [conicEvaluation_t, conicSecondParameterEquiv_symm_t, conicZeroPuncture_inverseT,
      map_neg]
  · change conicEvaluation _ _ _ _ _ (conicV _ _) = conicZeroPuncture c hc
      ((conicSecondParameterEquiv W.a₁ c ha).symm (algebraMap C₀ O₂ (conicV W.a₁ c)))
    rw [conicEvaluation_v, conicSecondParameterEquiv_symm_v, conicInverseV_of_zero c hc,
      zero_sub, map_neg, AlgHom.commutes]
    rfl

/-- The first punctured spectrum map factors the original first conic parameter immersion. -/
theorem conicPuncturedFirst_spec :
    Spec.map (CommRingCat.ofHom (conicPuncturedFirst W c hc).toRingHom) =
      Spec.map (CommRingCat.ofHom (conicZeroPuncture c hc).toRingHom) ≫
        (conicFirstParameterIso W.a₁ c ha).inv ≫ conicFirstOpenImmersion W.a₁ c := by
  rw [conicPuncturedFirst_parameter c hc W ha]
  change Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- The second punctured spectrum map factors the original second conic parameter immersion. -/
theorem conicPuncturedSecond_spec :
    Spec.map (CommRingCat.ofHom (conicPuncturedSecond W c hc).toRingHom) =
      Spec.map (CommRingCat.ofHom (conicZeroPuncture c hc).toRingHom) ≫
        (conicSecondParameterIso W.a₁ c ha).inv ≫ conicSecondOpenImmersion W.a₁ c := by
  rw [conicPuncturedSecond_parameter c hc W ha]
  change Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX

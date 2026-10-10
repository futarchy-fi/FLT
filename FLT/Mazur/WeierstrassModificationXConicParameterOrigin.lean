/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicInverseCoordinates

/-!
# The incidence section of the parameter line

Evaluation at zero extends across the denominator 1-c*z². Its scheme-theoretic
zero section is exactly the quotient by z, with coordinate algebra R.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (c : R)
local notation "P" => ConicParameterOpen c

/-- Evaluation at zero on the actual localized parameter line. -/
def conicParameterOrigin : P →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom (f := aeval (0 : R)) (conicParameterPolynomial c) (by
    simp [conicParameterPolynomial])

/-- The origin map restricts to the original polynomial evaluation. -/
theorem conicParameterOrigin_base (p : R[X]) :
    conicParameterOrigin c (algebraMap R[X] P p) = p.eval 0 := by
  rw [conicParameterOrigin, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  exact Polynomial.aeval_def _ _

/-- The original parameter vanishes at its origin. -/
@[simp] theorem conicParameterOrigin_z : conicParameterOrigin c (conicParameterZ c) = 0 := by
  rw [conicParameterZ, conicParameterOrigin_base, eval_X]

/-- The chosen denominator inverse is one at the origin. -/
@[simp] theorem conicParameterOrigin_inv : conicParameterOrigin c (conicParameterInv c) = 1 := by
  have h := congrArg (conicParameterOrigin c) (conicParameter_mul_inv c)
  simpa only [map_mul, map_sub, map_one, map_pow, AlgHom.commutes, conicParameterOrigin_z,
    zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, one_mul] using h

/-- The inverse incidence coordinate is zero at the parameter origin. -/
@[simp] theorem conicParameterOrigin_inverseT (a : R) :
    conicParameterOrigin c (conicInverseT a c) = 0 := by
  simp only [conicInverseT, map_mul, conicParameterOrigin_z, mul_zero, zero_mul]

/-- The inverse first slope is zero at the parameter origin. -/
@[simp] theorem conicParameterOrigin_inverseV (a : R) :
    conicParameterOrigin c (conicInverseV a c) = 0 := by
  simp only [conicInverseV, map_mul, map_pow, conicParameterOrigin_z,
    zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul]

/-- The ideal of the actual parameter origin. -/
def conicParameterOriginIdeal : Ideal P := Ideal.span {conicParameterZ c}

/-- Evaluation factors through the scheme-theoretic origin. -/
def conicParameterOriginQuotient : (P ⧸ conicParameterOriginIdeal c) →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (conicParameterOrigin c) (by
    change conicParameterOriginIdeal c ≤ RingHom.ker (conicParameterOrigin c)
    rw [conicParameterOriginIdeal, Ideal.span_le, Set.singleton_subset_iff]
    exact conicParameterOrigin_z c)

/-- Modulo the original parameter, every function is its value at the origin. -/
theorem conicParameterOrigin_quotient_map :
    (Algebra.ofId R (P ⧸ conicParameterOriginIdeal c)).comp (conicParameterOrigin c) =
      Ideal.Quotient.mkₐ R (conicParameterOriginIdeal c) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (conicParameterPolynomial c))
  apply Polynomial.algHom_ext
  change algebraMap R _ (conicParameterOrigin c (conicParameterZ c)) =
    Ideal.Quotient.mk _ (conicParameterZ c)
  rw [conicParameterOrigin_z, map_zero]
  symm
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- The entire scheme-theoretic origin is exactly one copy of the coefficient ring. -/
def conicParameterOriginEquiv : (P ⧸ conicParameterOriginIdeal c) ≃ₐ[R] R := by
  apply AlgEquiv.ofAlgHom (conicParameterOriginQuotient c) (Algebra.ofId R _)
  · apply AlgHom.ext
    intro r
    exact (conicParameterOriginQuotient c).commutes r
  · apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro q
    exact DFunLike.congr_fun (conicParameterOrigin_quotient_map c) q

/-- The origin equivalence evaluates each original parameter function at zero. -/
theorem conicParameterOriginEquiv_mk (q : P) :
    conicParameterOriginEquiv c (Ideal.Quotient.mk _ q) = conicParameterOrigin c q := rfl

end FLT.Mazur.WeierstrassModificationX

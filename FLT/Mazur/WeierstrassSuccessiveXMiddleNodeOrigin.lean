/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleNodeCoordinates

/-!
# The origin of the full localized middle node

Evaluation at z=u=0 extends over the denominator 1-c*z² for every coefficient
ring. The intersection of the two branches is exactly the coefficient scheme.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
variable {R : Type*} [CommRing R] (c : R)
local notation "B" => SuccessiveIncidence.Coordinate (0 : R)
local notation "N" => MiddleNodeOpen c

/-- The origin lies in the full localized node, without a condition on c. -/
def middleNodeOrigin : N →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom
    (f := SuccessiveIncidence.evaluation 0 (0 : R) 0 (by simp))
    (middleNodeDenominator c) (by
      simp only [middleNodeDenominator, map_sub, map_one, map_mul, map_pow,
        SuccessiveIncidence.evaluation_t, zero_pow (by decide : 2 ≠ 0), mul_zero,
        sub_zero, isUnit_one])

/-- The localization evaluation retains the original incidence evaluation. -/
theorem middleNodeOrigin_base (x : B) :
    middleNodeOrigin c (algebraMap B N x) =
      SuccessiveIncidence.evaluation 0 (0 : R) 0 (by simp) x := by
  rw [middleNodeOrigin, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The first branch coordinate vanishes at the origin. -/
@[simp] theorem middleNodeOrigin_z : middleNodeOrigin c (middleNodeZ c) = 0 := by
  rw [middleNodeZ, middleNodeOrigin_base, SuccessiveIncidence.evaluation_t]

/-- The second branch coordinate vanishes at the origin. -/
@[simp] theorem middleNodeOrigin_u : middleNodeOrigin c (middleNodeU c) = 0 := by
  rw [middleNodeU, middleNodeOrigin_base, SuccessiveIncidence.evaluation_u]

/-- The original incidence coordinate vanishes at the origin. -/
@[simp] theorem middleNodeOrigin_t (a : R) :
    middleNodeOrigin c (middleNodeT a c) = 0 := by
  rw [← middleNode_parameter_mul, map_mul, middleNodeOrigin_z, zero_mul]

/-- The first oriented slope vanishes at the origin. -/
@[simp] theorem middleNodeOrigin_v (a : R) :
    middleNodeOrigin c (middleNodeV a c) = 0 := by
  simp only [middleNodeV, WeierstrassModificationX.conicInverseV, map_mul,
    map_pow, conicParameterToMiddleNode_z, middleNodeOrigin_z,
    zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul]

/-- Both branch equations define the scheme-theoretic origin. -/
def middleNodeOriginIdeal : Ideal N := Ideal.span {middleNodeZ c, middleNodeU c}

/-- Origin evaluation descends through both branch equations. -/
def middleNodeOriginQuotient : (N ⧸ middleNodeOriginIdeal c) →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (middleNodeOrigin c) (by
    change middleNodeOriginIdeal c ≤ RingHom.ker (middleNodeOrigin c)
    rw [middleNodeOriginIdeal, Ideal.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact middleNodeOrigin_z c
    · exact middleNodeOrigin_u c)

/-- Every function modulo the two branches is its origin value. -/
theorem middleNodeOrigin_quotient_map :
    (Algebra.ofId R (N ⧸ middleNodeOriginIdeal c)).comp (middleNodeOrigin c) =
      Ideal.Quotient.mkₐ R (middleNodeOriginIdeal c) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (middleNodeDenominator c))
  apply SuccessiveIncidence.hom_ext 0
  · change algebraMap R _ (middleNodeOrigin c (middleNodeZ c)) =
      Ideal.Quotient.mk _ (middleNodeZ c)
    rw [middleNodeOrigin_z, map_zero]
    exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))).symm
  · change algebraMap R _ (middleNodeOrigin c (middleNodeU c)) =
      Ideal.Quotient.mk _ (middleNodeU c)
    rw [middleNodeOrigin_u, map_zero]
    exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))).symm

/-- The full scheme-theoretic intersection of the middle branches is the base ring. -/
def middleNodeOriginEquiv : (N ⧸ middleNodeOriginIdeal c) ≃ₐ[R] R := by
  apply AlgEquiv.ofAlgHom (middleNodeOriginQuotient c) (Algebra.ofId R _)
  · apply AlgHom.ext
    intro x
    exact (middleNodeOriginQuotient c).commutes x
  · apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro x
    exact DFunLike.congr_fun (middleNodeOrigin_quotient_map c) x

/-- The intersection equivalence evaluates the original node functions. -/
theorem middleNodeOriginEquiv_mk (x : N) :
    middleNodeOriginEquiv c (Ideal.Quotient.mk _ x) = middleNodeOrigin c x := rfl

end FLT.Mazur.WeierstrassSuccessiveX

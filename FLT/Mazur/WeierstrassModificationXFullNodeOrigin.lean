/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeBranches

/-!
# The scheme-theoretic origin of the full node chart

Evaluation at p=q=0 extends to the node open when a is a unit. The quotient
by both branches is exactly R, including over nonreduced coefficient rings.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R) (ha : IsUnit a)
local notation "N" => NodalFiber.Coordinate (0 : R)
local notation "L" => FullNodeOpen a c
local notation "J" => fullNodeOriginIdeal a c

/-- The zero-coordinate evaluation extends across the actual node denominators. -/
def fullNodeOrigin : L →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom
    (f := NodalFiber.evaluation 0 (0 : R) 0 (by simp)) (fullNodeDenominator a c) (by
      simpa only [fullNodeDenominator, map_mul, map_add, map_sub, map_one, map_pow,
        NodalFiber.evaluation_p, NodalFiber.evaluation_q, AlgHom.commutes,
        zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, zero_add, mul_one] using
          ha.map (algebraMap R R))

/-- The origin map agrees with the original node evaluation. -/
theorem fullNodeOrigin_base (x : N) :
    fullNodeOrigin a c ha (algebraMap N L x) =
      NodalFiber.evaluation 0 (0 : R) 0 (by simp) x := by
  rw [fullNodeOrigin, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- The first node coordinate vanishes at the origin. -/
@[simp] theorem fullNodeOrigin_p : fullNodeOrigin a c ha (fullNodeP a c) = 0 := by
  rw [fullNodeP, fullNodeOrigin_base, NodalFiber.evaluation_p]
/-- The second node coordinate vanishes at the origin. -/
@[simp] theorem fullNodeOrigin_q : fullNodeOrigin a c ha (fullNodeQ a c) = 0 := by
  rw [fullNodeQ, fullNodeOrigin_base, NodalFiber.evaluation_q]

/-- The inverse incidence formula vanishes at the origin. -/
theorem fullNodeOrigin_inverseT : fullNodeOrigin a c ha (fullNodeInverseT a c) = 0 := by
  simp only [fullNodeInverseT, map_mul, fullNodeOrigin_p, mul_zero, zero_mul]
/-- The inverse slope formula vanishes at the first oriented origin. -/
theorem fullNodeOrigin_inverseV : fullNodeOrigin a c ha (fullNodeInverseV a c) = 0 := by
  simp only [fullNodeInverseV, map_add, map_mul, map_pow, fullNodeOrigin_p,
    fullNodeOrigin_q, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero]

/-- Evaluation descends to the scheme-theoretic intersection of the two branches. -/
def fullNodeOriginQuotient : (L ⧸ J) →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (fullNodeOrigin a c ha) (by
    change J ≤ RingHom.ker (fullNodeOrigin a c ha)
    rw [fullNodeOriginIdeal, sup_le_iff, Ideal.span_le, Ideal.span_le,
      Set.singleton_subset_iff, Set.singleton_subset_iff]
    exact ⟨fullNodeOrigin_p a c ha, fullNodeOrigin_q a c ha⟩)

/-- Modulo both branch coordinates, each function is its origin value. -/
theorem fullNodeOrigin_quotient_map :
    (Algebra.ofId R (L ⧸ J)).comp (fullNodeOrigin a c ha) = Ideal.Quotient.mkₐ R J := by
  apply IsLocalization.algHom_ext (Submonoid.powers (fullNodeDenominator a c))
  apply NodalFiber.hom_ext 0
  · change algebraMap R _ (fullNodeOrigin a c ha (fullNodeP a c)) =
      Ideal.Quotient.mk _ (fullNodeP a c)
    rw [fullNodeOrigin_p, map_zero]
    symm
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton _)))
  · change algebraMap R _ (fullNodeOrigin a c ha (fullNodeQ a c)) =
      Ideal.Quotient.mk _ (fullNodeQ a c)
    rw [fullNodeOrigin_q, map_zero]
    symm
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))

/-- The scheme-theoretic node origin is exactly the coefficient ring. -/
def fullNodeOriginEquiv : (L ⧸ J) ≃ₐ[R] R := by
  apply AlgEquiv.ofAlgHom (fullNodeOriginQuotient a c ha) (Algebra.ofId R _)
  · apply AlgHom.ext
    intro r
    exact (fullNodeOriginQuotient a c ha).commutes r
  · apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro x
    exact DFunLike.congr_fun (fullNodeOrigin_quotient_map a c ha) x

/-- The quotient equivalence evaluates the actual node functions at the origin. -/
theorem fullNodeOriginEquiv_mk (x : L) :
    fullNodeOriginEquiv a c ha (Ideal.Quotient.mk _ x) = fullNodeOrigin a c ha x := rfl

local notation "F" => FiberCoordinate a c
local notation "O" => FullFirstFiberOpen a c

/-- The original full fiber component intersection near the first tangent is R. -/
def fullFirstIncidenceEquiv :
    (O ⧸ (Ideal.span {algebraMap F O (fiberT a c)} ⊔
      Ideal.span {algebraMap F O (fiberConicFactor a c)})) ≃ₐ[R] R :=
  (fullFirstNodeIntersectionEquiv a c ha).trans (fullNodeOriginEquiv a c ha)

end FLT.Mazur.WeierstrassModificationX

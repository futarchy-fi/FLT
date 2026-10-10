/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberIntersection
public import Mathlib.RingTheory.Polynomial.Quotient

/-!
# The two scheme-theoretic intersection points

When a is a unit, the incidence-conic intersection is the product R × R.
Its ordered factors evaluate the original slope at 0 and -a, respectively.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (a : R)

/-- The two original slope ideals are comaximal over any split base. -/
theorem intersection_root_ideals_coprime (ha : IsUnit a) :
    IsCoprime (Ideal.span {X - C (0 : R)}) (Ideal.span {X - C (-a)}) := by
  rw [Ideal.isCoprime_span_singleton_iff]
  obtain ⟨u, rfl⟩ := ha
  refine ⟨-C (↑u⁻¹ : R), C (↑u⁻¹ : R), ?_⟩
  have hi : C (↑u⁻¹ : R) * C (↑u : R) = (1 : R[X]) := by
    rw [← map_mul, Units.inv_mul, map_one]
  simp only [map_zero, sub_zero, map_neg, sub_neg_eq_add]
  linear_combination hi

/-- Chinese remainders separate the two original intersection points as rings. -/
def intersectionSplitRingEquiv (ha : IsUnit a) : IntersectionCoordinate a ≃+* R × R :=
  (Ideal.quotEquivOfEq (show Ideal.span {X * (X + C a)} =
      Ideal.span {X - C (0 : R)} * Ideal.span {X - C (-a)} by
    rw [Ideal.span_singleton_mul_span_singleton]
    simp only [map_zero, sub_zero, map_neg, sub_neg_eq_add])).trans
      ((Ideal.quotientMulEquivQuotientProd _ _ (intersection_root_ideals_coprime a ha)).trans
        (RingEquiv.prodCongr (quotientSpanXSubCAlgEquiv (0 : R)).toRingEquiv
          (quotientSpanXSubCAlgEquiv (-a)).toRingEquiv))

/-- The first split factor evaluates the original slope at zero. -/
@[simp] theorem intersectionSplitRingEquiv_fst (ha : IsUnit a) (p : R[X]) :
    (intersectionSplitRingEquiv a ha (Ideal.Quotient.mk _ p)).1 = p.eval 0 := by
  rfl

/-- The second split factor evaluates the original slope at its oriented value -a. -/
@[simp] theorem intersectionSplitRingEquiv_snd (ha : IsUnit a) (p : R[X]) :
    (intersectionSplitRingEquiv a ha (Ideal.Quotient.mk _ p)).2 = p.eval (-a) := by
  rfl

/-- The actual two-point intersection is a disjoint pair over the original coefficient ring. -/
def intersectionSplitEquiv (ha : IsUnit a) : IntersectionCoordinate a ≃ₐ[R] R × R where
  __ := intersectionSplitRingEquiv a ha
  commutes' r := by
    apply Prod.ext
    · exact eval_C
    · exact eval_C

/-- The entire original fiber intersection is the ordered pair of sections 0 and -a. -/
def fiberIntersectionSplitEquiv (c : R) (ha : IsUnit a) :
    (FiberCoordinate a c ⧸ fiberIntersectionIdeal a c) ≃ₐ[R] R × R :=
  (fiberIntersectionEquiv a c).trans (intersectionSplitEquiv a ha)

end FLT.Mazur.WeierstrassModificationX

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IteratedQuotientProjection

/-!
# Principal arrows into literal iterated quotient targets

An inverse-coordinate equation and ideal preservation construct arrows from
principal quotient sources to the second localization of the target quotient.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.IteratedQuotientProjection

universe u v

variable {P : Type u} [CommRing P] (I : Ideal P) (r : P) (s : Localization.Away r)
  {Q : Type v} [CommRing Q] (J : Ideal Q) (a : Q)
  (f : Q →+* Localization.Away s)
  (hf : J ≤ ((I.map (algebraMap P (Localization.Away r))).map
    (algebraMap _ (Localization.Away s))).comap f)
  (v : Localization.Away s)
  (hv : f a * v - 1 ∈ (I.map (algebraMap P (Localization.Away r))).map
    (algebraMap _ (Localization.Away s)))

/-- Descend the ambient arrow into the actual double localization of the quotient. -/
def quotientArrow : Q ⧸ J →+* Target I r s :=
  Ideal.Quotient.lift J ((projection I r s).comp f) fun x hx ↦ by
    have h := hf hx
    rw [← ker_projection] at h
    exact h

/-- The quotient arrow retains its unquotiented numerator representative. -/
@[simp] theorem quotientArrow_mk (x : Q) :
    quotientArrow I r s J f hf (Ideal.Quotient.mk J x) = projection I r s (f x) := rfl

include hv in
/-- A single inverse-coordinate relation supplies invertibility in the actual target. -/
theorem quotientArrow_denominator_isUnit :
    IsUnit (quotientArrow I r s J f hf (Ideal.Quotient.mk J a)) := by
  rw [quotientArrow_mk]
  apply isUnit_iff_exists_inv.mpr
  refine ⟨projection I r s v, ?_⟩
  have h : projection I r s (f a * v - 1) = 0 := by
    rw [← RingHom.mem_ker, ker_projection]
    exact hv
  simpa only [map_sub, map_mul, map_one, sub_eq_zero] using h

/-- An arrow between the canonical source and target principal quotient rings. -/
def principalArrow : PrincipalQuotientProjection.Target J a →+* Target I r s :=
  IsLocalization.Away.lift (Ideal.Quotient.mk J a)
    (quotientArrow_denominator_isUnit I r s J a f hf v hv)

/-- The principal arrow agrees with the polynomial representative on every ambient element. -/
@[simp] theorem principalArrow_numerator (x : Q) :
    principalArrow I r s J a f hf v hv
      (algebraMap (Q ⧸ J) (PrincipalQuotientProjection.Target J a) (Ideal.Quotient.mk J x)) =
      projection I r s (f x) := by
  exact IsLocalization.Away.lift_eq _ _ _

end FLT.Mazur.IteratedQuotientProjection

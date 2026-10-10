/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalQuotientProjection

/-!
# Arrows between canonical principal quotients

An inverse-coordinate relation in the target ideal makes the source denominator
invertible after imposing finite relations. This constructs a map between the
literal principal localizations of both chosen ambient quotient rings.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PrincipalQuotientProjection

universe u v

variable {P : Type u} [CommRing P] (I : Ideal P) (r : P)
  {Q : Type v} [CommRing Q] (J : Ideal Q) (a : Q)
  (f : Q →+* Localization.Away r)
  (hf : J ≤ (I.map (algebraMap P (Localization.Away r))).comap f)
  (v : Localization.Away r)
  (hv : f a * v - 1 ∈ I.map (algebraMap P (Localization.Away r)))

include hv in
/-- A single inverse-coordinate relation supplies invertibility in the actual target. -/
theorem quotientArrow_denominator_isUnit :
    IsUnit (quotientArrow I r J f hf (Ideal.Quotient.mk J a)) := by
  rw [quotientArrow_mk]
  apply isUnit_iff_exists_inv.mpr
  refine ⟨projection I r v, ?_⟩
  have h : projection I r (f a * v - 1) = 0 := by
    rw [← RingHom.mem_ker, ker_projection]
    exact hv
  simpa only [map_sub, map_mul, map_one, sub_eq_zero] using h

/-- An arrow between the canonical source and target principal quotient rings. -/
def principalArrow : Target J a →+* Target I r :=
  IsLocalization.Away.lift (Ideal.Quotient.mk J a)
    (quotientArrow_denominator_isUnit I r J a f hf v hv)

/-- The principal arrow agrees with the polynomial representative on every ambient element. -/
@[simp] theorem principalArrow_numerator (x : Q) :
    principalArrow I r J a f hf v hv
      (algebraMap (Q ⧸ J) (Target J a) (Ideal.Quotient.mk J x)) =
      projection I r (f x) := by
  exact IsLocalization.Away.lift_eq _ _ _

/-- Maps from the canonical principal quotient are determined on ambient numerators. -/
theorem hom_ext {T : Type*} [CommRing T] {g h : Target J a →+* T}
    (heq : ∀ x : Q,
      g (algebraMap (Q ⧸ J) (Target J a) (Ideal.Quotient.mk J x)) =
      h (algebraMap (Q ⧸ J) (Target J a) (Ideal.Quotient.mk J x))) : g = h := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk J a))
  apply Ideal.Quotient.ringHom_ext
  exact RingHom.ext heq

end FLT.Mazur.PrincipalQuotientProjection

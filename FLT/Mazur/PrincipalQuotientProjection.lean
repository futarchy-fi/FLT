/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalRelationClosure
public import Mathlib.RingTheory.Localization.Algebra

/-!
# Projection to the canonical localized quotient

Localizing a quotient map has exactly the extended relation ideal as kernel.
Maps preserving that ideal therefore descend into the actual principal open
of the quotient, rather than into an independently presented target.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PrincipalQuotientProjection

universe u v

variable {P : Type u} [CommRing P] (I : Ideal P) (r : P)

/-- The literal principal localization of the quotient ring. -/
abbrev Target := Localization.Away (Ideal.Quotient.mk I r)

/-- Projection from the unquotiented principal open to the canonical quotient open. -/
def projection : Localization.Away r →+* Target I r :=
  NoetherianRelationContraction.principalCoefficientMap (Ideal.Quotient.mk I) r

/-- Quotient projection sends a numerator to its quotient numerator. -/
@[simp] theorem projection_algebraMap (x : P) :
    projection I r (algebraMap P (Localization.Away r) x) =
      algebraMap (P ⧸ I) (Target I r) (Ideal.Quotient.mk I x) :=
  RingHom.congr_fun
    (NoetherianRelationContraction.principalCoefficientMap_comp (Ideal.Quotient.mk I) r) x

/-- Every element of the canonical localized quotient has an unquotiented representative. -/
theorem projection_surjective : Function.Surjective (projection I r) :=
  IsLocalization.map_surjective_of_surjective (Submonoid.powers r)
    (Localization.Away r) (Target I r) Ideal.Quotient.mk_surjective

/-- The kernel is precisely the localization of the ambient relation ideal. -/
theorem ker_projection :
    RingHom.ker (projection I r) = I.map (algebraMap P (Localization.Away r)) := by
  have h := IsLocalization.ker_map (S := Localization.Away r) (Target I r)
    (Ideal.Quotient.mk I) (Submonoid.map_powers (Ideal.Quotient.mk I) r)
  change RingHom.ker (projection I r) =
    (RingHom.ker (Ideal.Quotient.mk I)).map (algebraMap P (Localization.Away r)) at h
  simpa only [Ideal.mk_ker] using h

variable {Q : Type v} [CommRing Q] (J : Ideal Q) (f : Q →+* Localization.Away r)
  (hf : J ≤ (I.map (algebraMap P (Localization.Away r))).comap f)

/-- A relation-preserving arrow lands in the canonical principal quotient target. -/
def quotientArrow : Q ⧸ J →+* Target I r :=
  Ideal.Quotient.lift J ((projection I r).comp f) fun x hx ↦ by
    have h := hf hx
    rw [← ker_projection] at h
    exact h

/-- The descended arrow agrees with the original polynomial arrow on every numerator. -/
@[simp] theorem quotientArrow_mk (x : Q) :
    quotientArrow I r J f hf (Ideal.Quotient.mk J x) = projection I r (f x) := rfl

end FLT.Mazur.PrincipalQuotientProjection

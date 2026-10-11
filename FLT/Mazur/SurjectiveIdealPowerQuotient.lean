/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Ideal-power neighborhoods under a surjective ring map

A surjective map whose kernel lies in the n-th power of an ideal preserves
that ideal-power neighborhood, with its original map on representatives.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.SurjectiveIdealPowerQuotient

variable {A B : Type*} [CommRing A] [CommRing B]
  (f : A →+* B) (hf : Function.Surjective f) (J : Ideal A) (n : ℕ)

/-- The quotient of the target by the image ideal power. -/
def toQuotient : A →+* B ⧸ J.map f ^ n := (Ideal.Quotient.mk _).comp f

include hf in
/-- The target quotient has precisely the original ideal-power kernel. -/
theorem toQuotient_ker (hker : RingHom.ker f ≤ J ^ n) :
    RingHom.ker (toQuotient f J n) = J ^ n := by
  rw [toQuotient, ← RingHom.comap_ker, Ideal.mk_ker, ← Ideal.map_pow,
    Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot,
    sup_eq_left.mpr hker]

include hf in
/-- Every target neighborhood section has an original representative. -/
theorem toQuotient_surjective : Function.Surjective (toQuotient f J n) :=
  Ideal.Quotient.mk_surjective.comp hf

/-- The actual ideal-power neighborhood comparison induced by the surjection. -/
def equivalence (hker : RingHom.ker f ≤ J ^ n) :
    (A ⧸ J ^ n) ≃+* (B ⧸ J.map f ^ n) :=
  (Ideal.quotEquivOfEq (toQuotient_ker f hf J n hker).symm).trans
    (RingHom.quotientKerEquivOfSurjective (toQuotient_surjective f hf J n))

/-- The neighborhood comparison retains the original ring map on every representative. -/
@[simp] theorem equivalence_mk (hker : RingHom.ker f ≤ J ^ n) (a : A) :
    equivalence f hf J n hker (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (f a) := by
  rw [equivalence, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

end FLT.Mazur.SurjectiveIdealPowerQuotient

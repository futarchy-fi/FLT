/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# A full quotient presentation after killing one parameter

A surjective restriction followed by a parameter quotient has kernel equal
to the original restriction kernel plus the original lifted parameter ideal.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.SurjectiveParameterQuotient
variable {A B : Type*} [CommRing A] [CommRing B]
variable (f : A →+* B) (hf : Function.Surjective f) (t : A)
include hf

/-- Killing the image parameter retains the entire original restriction kernel. -/
theorem kernel :
    RingHom.ker ((Ideal.Quotient.mk (Ideal.span {f t})).comp f) =
      RingHom.ker f ⊔ Ideal.span {t} := by
  have he : Ideal.map f (Ideal.span {t}) = Ideal.span {f t} := by
    rw [Ideal.map_span, Set.image_singleton]
  calc
    RingHom.ker ((Ideal.Quotient.mk (Ideal.span {f t})).comp f) =
        Ideal.comap f (Ideal.span {f t}) := by
      ext z
      exact Ideal.Quotient.eq_zero_iff_mem
    _ = Ideal.comap f (Ideal.map f (Ideal.span {t})) := congrArg _ he.symm
    _ = Ideal.span {t} ⊔ Ideal.comap f ⊥ := Ideal.comap_map_of_surjective f hf _
    _ = RingHom.ker f ⊔ Ideal.span {t} := sup_comm _ _

/-- The original ambient quotient is the full parameter fiber, including nilpotents. -/
def equiv : A ⧸ (RingHom.ker f ⊔ Ideal.span {t}) ≃+* B ⧸ Ideal.span {f t} :=
  (Ideal.quotEquivOfEq (kernel f hf t).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := (Ideal.Quotient.mk (Ideal.span {f t})).comp f)
      (Ideal.Quotient.mk_surjective.comp hf))

/-- Every representative is restricted and then reduced by the original parameter. -/
theorem equiv_mk (z : A) :
    equiv f hf t (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ (f z) := rfl

end FLT.Mazur.SurjectiveParameterQuotient

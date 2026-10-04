/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.LocalizedFinitePresentation

/-! # Lift reduced local presentations without a Noetherian base hypothesis -/

@[expose] public noncomputable section

namespace AlgHom

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A]
  [Algebra.FinitePresentation R S] [Algebra.FinitePresentation R A] [Module.Flat R A]

/-- At each target prime, finite presentation supplies a finite kernel and the
contracted base prime supplies the radical ideal needed for Nakayama lifting.
The target localization inherits flatness from the original target. -/
theorem exists_presentationAtPrime_of_modBaseIdeal
    (f : S →ₐ[R] A) (hf : Function.Surjective f) (Q : Ideal A) [Q.IsPrime]
    (J : Ideal R) (hJ : J ≤ Q.comap (algebraMap R A)) {n : ℕ}
    (v : Fin n → Localization.AtPrime (Q.comap (f : S →+* A)) ⧸
      J.map (algebraMap R (Localization.AtPrime (Q.comap (f : S →+* A)))))
    (hv : Ideal.span (Set.range v) = RingHom.ker ((f.presentationAtPrime Q).modBaseIdeal J)) :
    ∃ (w : Fin n → Localization.AtPrime (Q.comap (f : S →+* A)))
      (e : (Localization.AtPrime (Q.comap (f : S →+* A)) ⧸ Ideal.span (Set.range w)) ≃ₐ[R]
        Localization.AtPrime Q),
      (∀ i, Ideal.Quotient.mk _ (w i) = v i) ∧
      ∀ s, e (Ideal.Quotient.mk _ s) = f.presentationAtPrime Q s := by
  have : Module.Flat R (Localization.AtPrime Q) := Module.Flat.trans R A _
  exact (f.presentationAtPrime Q).exists_presentation_of_flat_modBaseIdeal
    (f.presentationAtPrime_surjective hf Q) (f.ker_presentationAtPrime_fg hf Q) J
    ((Ideal.map_mono hJ).trans (f.baseIdeal_le_jacobson_presentationAtPrime Q)) v hv

end AlgHom

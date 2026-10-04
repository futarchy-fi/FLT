/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.LocalizedFinitePresentation
public import Mathlib.RingTheory.Artinian.Ring

/-! # Artinian quotients of localizations of a presentation -/

@[expose] public noncomputable section

namespace AlgHom

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [IsArtinianRing A]

/-- Localizing a presentation of an Artinian algebra has Artinian quotient at every
prime containing the original kernel. -/
theorem isArtinianRing_quotient_localized_kernel (f : S →ₐ[R] A)
    (hf : Function.Surjective f) (P : Ideal S) [P.IsPrime] (hP : RingHom.ker f ≤ P) :
    IsArtinianRing (Localization.AtPrime P ⧸
      (RingHom.ker f).map (algebraMap S (Localization.AtPrime P))) := by
  let Q := P.map (f : S →+* A)
  have : Q.IsPrime := Ideal.map_isPrime_of_surjective hf hP
  have he : Q.comap (f : S →+* A) = P := by
    rw [Ideal.comap_map_of_surjective (f : S →+* A) hf]
    exact sup_eq_left.mpr hP
  have h : IsArtinianRing (Localization.AtPrime (Q.comap (f : S →+* A)) ⧸
      (RingHom.ker f).map
        (algebraMap S (Localization.AtPrime (Q.comap (f : S →+* A))))) := by
    rw [← f.ker_presentationAtPrime hf Q]
    exact (Ideal.quotientKerAlgEquivOfSurjective
      (f.presentationAtPrime_surjective hf Q)).symm.toRingEquiv.isArtinianRing
  have transport (P' : Ideal S) [P'.IsPrime] (he' : Q.comap (f : S →+* A) = P') :
      IsArtinianRing (Localization.AtPrime P' ⧸
        (RingHom.ker f).map (algebraMap S (Localization.AtPrime P'))) := by
    subst P'
    exact h
  exact transport P he

end AlgHom

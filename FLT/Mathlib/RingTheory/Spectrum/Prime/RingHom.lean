/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Maps from finite products of fields
-/

@[expose] public section

/-- A homomorphism from a finite product of fields to a domain factors through one coordinate. -/
theorem RingHom.exists_eq_comp_eval
    {ι : Type*} [_root_.Finite ι] {F : ι → Type*} [∀ i, Field (F i)]
    {E : Type*} [CommRing E] [IsDomain E] (f : (∀ i, F i) →+* E) :
    ∃ (i : ι) (g : F i →+* E), g.comp (Pi.evalRingHom F i) = f := by
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
    (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum (∀ i, F i))
  have hqbot : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime q.asIdeal
  have hk : RingHom.ker (Pi.evalRingHom F i) ≤ RingHom.ker f := by
    have h := congrArg PrimeSpectrum.asIdeal hq
    change Ideal.comap (Pi.evalRingHom F i) q.asIdeal = RingHom.ker f at h
    rw [hqbot, ← RingHom.ker_eq_comap_bot] at h
    exact le_of_eq h
  exact ⟨i, (Pi.evalRingHom F i).liftOfSurjective
    (RingHomSurjective.is_surjective) ⟨f, hk⟩,
    RingHom.liftOfSurjective_comp _ _ _⟩


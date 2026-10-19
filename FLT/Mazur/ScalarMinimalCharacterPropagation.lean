/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarAlgebraicClosureTests
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Propagate character vanishing from minimal scalar branches

Going down lifts a minimal scalar prime below each original coefficient prime.
An ideal vanishing on those generic fibers therefore vanishes at every prime
in the full scalar localization. Flatness supplies going down; finite type
allows testing each generic fiber in its canonical residue closure.
-/

@[expose] public noncomputable section
universe u
namespace FLT.Mazur.ScalarTestLocalization
variable {R B : Type u} [CommRing R] [CommRing B]
  (s : R →+* B) (P : PrimeSpectrum R) (J : Ideal B)

/-- Going down propagates generic-fiber ideal containment to the full scalar localization. -/
theorem ideal_le_prime_of_minimal_scalar_fibers
    (hg : GeneralizingMap (PrimeSpectrum.comap s))
    (hJ : ∀ Q : PrimeSpectrum R, Q.asIdeal ∈ minimalPrimes R → Q ≤ P →
      ∀ q : PrimeSpectrum B, PrimeSpectrum.comap s q = Q → J ≤ q.asIdeal)
    (q : PrimeSpectrum B) (hq : PrimeSpectrum.comap s q ≤ P) : J ≤ q.asIdeal := by
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_minimalPrimes_le
    (J := (PrimeSpectrum.comap s q).asIdeal) bot_le
  let Q' : PrimeSpectrum R := ⟨Q, hQ.1.1⟩
  have hQ' : Q' ≤ PrimeSpectrum.comap s q := hle
  obtain ⟨q', hq', he⟩ := hg ((PrimeSpectrum.le_iff_specializes _ _).mp hQ')
  exact (hJ Q' hQ (hQ'.trans hq) q' he).trans
    ((PrimeSpectrum.le_iff_specializes _ _).mpr hq')

/-- Canonical geometric characters on minimal branches control every original local prime. -/
theorem ideal_le_prime_of_minimal_scalar_characters (hs : s.FiniteType)
    (hg : GeneralizingMap (PrimeSpectrum.comap s))
    (hJ : ∀ Q : PrimeSpectrum R, Q.asIdeal ∈ minimalPrimes R → Q ≤ P →
      ∀ χ : B →+* AlgebraicClosure Q.asIdeal.ResidueField,
        χ.comp s = algebraMap R _ → J ≤ RingHom.ker χ)
    (q : PrimeSpectrum B) (hq : PrimeSpectrum.comap s q ≤ P) : J ≤ q.asIdeal := by
  apply ideal_le_prime_of_minimal_scalar_fibers s P J hg _ q hq
  intro Q hQ hQP q' he t ht
  apply (residueGeometricTest_iff_original_fiber s Q hs t).mp _ q' he
  exact (residueGeometricTest_iff s Q t).mpr (fun χ hχ ↦ hJ Q hQ hQP χ hχ ht)

/-- Full character containment propagates to every generization of the original scalar prime. -/
theorem ideal_le_character_of_minimal_scalar_characters (hs : s.FiniteType)
    (hg : GeneralizingMap (PrimeSpectrum.comap s))
    (hJ : ∀ Q : PrimeSpectrum R, Q.asIdeal ∈ minimalPrimes R → Q ≤ P →
      ∀ χ : B →+* AlgebraicClosure Q.asIdeal.ResidueField,
        χ.comp s = algebraMap R _ → J ≤ RingHom.ker χ)
    (Q : PrimeSpectrum R) (hQP : Q ≤ P)
    (χ : B →+* AlgebraicClosure Q.asIdeal.ResidueField)
    (hχ : χ.comp s = algebraMap R _) : J ≤ RingHom.ker χ := by
  have hc : PrimeSpectrum.comap s (PrimeSpectrum.comap χ ⊥) = Q := by
    change PrimeSpectrum.comap (χ.comp s) ⊥ = Q
    rw [hχ, algebraicClosure_residue_center]
  exact ideal_le_prime_of_minimal_scalar_characters s P J hs hg hJ
    (PrimeSpectrum.comap χ ⊥) (hc.le.trans hQP)

/-- Flatness is a sufficient geometric hypothesis for propagation from generic characters. -/
theorem flat_ideal_le_character_of_minimal_scalar_characters (hs : s.FiniteType)
    (hf : s.Flat)
    (hJ : ∀ Q : PrimeSpectrum R, Q.asIdeal ∈ minimalPrimes R → Q ≤ P →
      ∀ χ : B →+* AlgebraicClosure Q.asIdeal.ResidueField,
        χ.comp s = algebraMap R _ → J ≤ RingHom.ker χ)
    (Q : PrimeSpectrum R) (hQP : Q ≤ P)
    (χ : B →+* AlgebraicClosure Q.asIdeal.ResidueField)
    (hχ : χ.comp s = algebraMap R _) : J ≤ RingHom.ker χ :=
  ideal_le_character_of_minimal_scalar_characters s P J hs
    hf.generalizingMap_comap hJ Q hQP χ hχ

end FLT.Mazur.ScalarTestLocalization

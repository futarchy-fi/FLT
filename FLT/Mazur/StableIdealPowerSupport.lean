/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Stable ideal powers force an open closed zero locus

A finitely generated stable positive power is idempotent. Its idempotent
generator shows that the zero locus of the original ideal is open closed.
This supplies the converse geometric test for power stabilization.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.StableIdealPowerSupport
variable {R : Type*} [CommRing R] (I : Ideal R) (K : ℕ)

/-- Equality of consecutive powers makes the first stable positive power idempotent. -/
theorem isIdempotentElem_pow_of_succ_eq
    (hK : I ^ (K + 1 + 1) = I ^ (K + 1)) :
    IsIdempotentElem (I ^ (K + 1)) := by
  have hs : ∀ l, K ≤ l → I ^ (l + 1) = I ^ (K + 1) := by
    intro l hl
    induction l, hl using Nat.le_induction with
    | base => rfl
    | succ l _ ih => rw [pow_succ, ih, ← pow_succ, hK]
  change I ^ (K + 1) * I ^ (K + 1) = I ^ (K + 1)
  rw [← pow_add]
  simpa only [Nat.add_assoc, Nat.add_left_comm] using
    hs (K + (K + 1)) (Nat.le_add_right _ _)

/-- Finite generation prevents a non-open zero locus from having stationary powers. -/
theorem isClopen_zeroLocus_of_succ_eq (hfg : (I ^ (K + 1)).FG)
    (hK : I ^ (K + 1 + 1) = I ^ (K + 1)) :
    IsClopen (PrimeSpectrum.zeroLocus (I : Set R)) := by
  obtain ⟨e, he, hspan⟩ := (Ideal.isIdempotentElem_iff_of_fg _ hfg).mp
    (isIdempotentElem_pow_of_succ_eq I K hK)
  apply PrimeSpectrum.isClopen_iff_zeroLocus.mpr
  refine ⟨e, he, ?_⟩
  rw [← PrimeSpectrum.zeroLocus_pow I (Nat.succ_ne_zero K), hspan]
  exact PrimeSpectrum.zeroLocus_span {e}

end FLT.Mazur.StableIdealPowerSupport

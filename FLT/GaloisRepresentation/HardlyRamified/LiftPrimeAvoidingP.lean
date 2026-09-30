/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Nilpotent.Lemmas

/-! # A prime ideal avoiding a nonnilpotent coefficient prime -/

@[expose] public section

namespace GaloisRepresentation.IsHardlyRamified

/-- A nonnilpotent coefficient prime is avoided by some prime ideal.
The nonnilpotence assumption must come from the arithmetic ring construction. -/
theorem exists_prime_avoiding_p (D : Type) [CommRing D] (p : ℕ)
    (h : ¬ IsNilpotent (p : D)) :
    ∃ P : Ideal D, P.IsPrime ∧ (p : D) ∉ P := by
  simpa only [nilpotent_iff_mem_prime, not_forall, exists_prop] using h

end GaloisRepresentation.IsHardlyRamified

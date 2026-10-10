/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PadicValuationRing
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Arithmetic inputs for the rational p-adic valuation ring

The actual valuation subring is a DVR with uniformizer p and residue field
of exactly p elements. These discharge the arithmetic inputs of the local
semistability and component theorems at the rational primes 2, 3 and p.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing

variable (p : ℕ) [Fact p.Prime]

/-- The actual p-adic valuation subring is a discrete valuation ring. -/
theorem padicIntegerSubring_isDiscreteValuationRing :
    IsDiscreteValuationRing (padicIntegerSubring p) :=
  inferInstanceAs (IsDiscreteValuationRing ℤ_[p])

/-- The rational prime itself is a uniformizer, so the rational p-adic base is unramified. -/
theorem padicIntegerSubring_irreducible_prime : Irreducible (p : padicIntegerSubring p) :=
  PadicInt.irreducible_p

/-- The actual p-adic residue field is finite. -/
theorem padicIntegerSubring_residue_finite : Finite (ResidueField (padicIntegerSubring p)) :=
  Finite.of_equiv (ZMod p) (PadicInt.residueField (p := p)).symm.toEquiv

/-- The actual p-adic residue field has exactly p elements. -/
theorem padicIntegerSubring_residue_card : Nat.card (ResidueField (padicIntegerSubring p)) = p :=
  (Nat.card_congr (PadicInt.residueField (p := p)).toEquiv).trans (Nat.card_zmod p)

end FLT.Mazur

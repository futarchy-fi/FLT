/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterPrimeQuotient
public import FLT.GroupScheme.RaynaudFundamentalDigitUnit

/-!
# The fundamental universal constant is p times a unit

Apply the divided group-algebra calculation to the constructed fundamental
character. The quotient has residue -1, hence is a unit of the local base.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing CharacterAverage

variable {R F : Type} [CommRing R] [IsDomain R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)] [Field F] [Fintype F] [DecidableEq F]
  [Invertible (Fintype.card Fˣ : R)]
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (e : F →+* ResidueField R)

/-- The actual fundamental constant is p times a unit with residue -1. -/
theorem fundamental_constant_eq_prime_mul_unit :
    ∃ u : Rˣ,
      constant (fundamentalCharacter p e) (fundamentalCharacter p e ^ p) p =
        (p : R) * u ∧ residue R (u : R) = -1 := by
  let : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  obtain ⟨u, hu, hr⟩ := exists_prime_quotient (fundamentalCharacter p e) e p
    (fundamentalCharacter_residue p e)
  have hunit : IsUnit u := (residue_ne_zero_iff_isUnit u).mp (by
    change algebraMap R (ResidueField R) u ≠ 0
    rw [hr]
    exact neg_ne_zero.mpr one_ne_zero)
  exact ⟨hunit.unit, by simpa using hu, by simpa using hr⟩

end ThreeAdicPlan

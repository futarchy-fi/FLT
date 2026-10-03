/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudFundamentalPrimeUnit

/-!
# Unit constants for all residue-embedding characters

The arithmetic calculation applies to any character whose reduction is a
field embedding. This includes every Frobenius twist in the fundamental
cycle, without identifying or assuming any model parameter.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CharacterAverage
open IsLocalRing

variable {R F : Type} [CommRing R] [IsLocalRing R] [Field F] [Finite F] [Fintype Fˣ]
  [Invertible (Fintype.card Fˣ : R)]
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (χ : Fˣ →* Rˣ) (e : F →+* ResidueField R)
  (he : ∀ u : Fˣ, residue R (χ u : R) = e u)

include he in
/-- Every residue-embedding character has a p-fold constant equal to p times a unit. -/
theorem constant_eq_prime_mul_unit :
    ∃ u : Rˣ, constant χ (χ ^ p) p = (p : R) * u ∧ residue R (u : R) = -1 := by
  let : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  obtain ⟨u, hu, hr⟩ := exists_prime_quotient χ e p he
  have hunit : IsUnit u := (residue_ne_zero_iff_isUnit u).mp (by
    change algebraMap R (ResidueField R) u ≠ 0
    rw [hr]
    exact neg_ne_zero.mpr one_ne_zero)
  exact ⟨hunit.unit, by simpa using hu, by simpa using hr⟩

include he in
/-- Below p, a single residue-embedding character has unit repeated constants. -/
theorem isUnit_digit_constant (n : ℕ) (hn : n ≠ 0) (hnp : n < p) :
    IsUnit (constant χ (χ ^ n) n) := by
  let : Invertible (Fintype.card Fˣ : ResidueField R) :=
    (Invertible.map (residue R) (Fintype.card Fˣ : R)).copy _ (map_natCast _ _).symm
  apply (residue_ne_zero_iff_isUnit _).mp
  rw [map_constant]
  have hpow : mapCharacter (residue R) (χ ^ n) = mapCharacter (residue R) χ ^ n := by
    ext u
    simp [mapCharacter]
  rw [hpow, constant_embedding_factorial _ e he n hn]
  let : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  exact ((IsUnit.natCast_factorial_iff_of_charP p).mpr hnp).ne_zero

end ThreeAdicPlan.CharacterAverage

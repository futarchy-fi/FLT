/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudDigitBinomialUnit
public import FLT.GroupScheme.RaynaudFundamentalCharacter

/-!
# Mixed digit constants are units

Reduction of a lifted character identifies the mixed constant with the
explicit digit binomial product. Its residue is a product of factorials
of numbers less than p, so the original local-ring constant is a unit.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CharacterAverage
open IsLocalRing

variable {R F : Type} [CommRing R] [IsLocalRing R] [Field F] [Fintype Fˣ]
  [Invertible (Fintype.card Fˣ : R)] (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (χ : Fˣ →* Rˣ) (e : F →+* ResidueField R)
  (he : ∀ u : Fˣ, residue R (χ u : R) = e u)

include he in
omit [Fintype Fˣ] [Invertible (Fintype.card Fˣ : R)] in
/-- Every character power reduces to the matching power of the embedding character. -/
theorem map_character_power (k : ℕ) :
    mapCharacter (residue R) (χ ^ k) = embeddingCharacter e ^ k := by
  ext u
  change residue R ((χ u : R) ^ k) = e u ^ k
  rw [map_pow, he]

include he in
/-- The residue of a mixed power constant is its explicit binomial product. -/
theorem mixed_power_constant_residue (ks : List ℕ) (hpos : ∀ k ∈ ks, 0 < k)
    (hne : ks.sum ≠ 0) (hq : ks.sum ≤ Fintype.card Fˣ) :
    residue R (mixedConstant (ks.reverse.map (fun k ↦ χ ^ k)) (χ ^ ks.sum)) =
      (weightCoefficient ks 0 : ResidueField R) := by
  let : Invertible (Fintype.card Fˣ : ResidueField R) :=
    (Invertible.map (residue R) (Fintype.card Fˣ : R)).copy _ (map_natCast _ _).symm
  rw [map_mixedConstant, map_character_power χ e he, List.map_map]
  simp_rw [Function.comp_def, map_character_power χ e he]
  exact mixed_power_constant e ks hpos hne hq

variable [Finite F]

include he in
/-- The mixed digit constant has residue equal to the product of digit factorials. -/
theorem mixed_digit_constant_residue (ds : List ℕ)
    (hne : Nat.ofDigits p ds ≠ 0) (hq : Nat.ofDigits p ds ≤ Fintype.card Fˣ) :
    residue R (mixedConstant ((digitWeights p ds).reverse.map (fun k ↦ χ ^ k))
      (χ ^ Nat.ofDigits p ds)) = ((ds.map Nat.factorial).prod : ResidueField R) := by
  let : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  rw [← digitWeights_sum p ds, mixed_power_constant_residue χ e he _
    (digitWeights_pos p (Fact.out : p.Prime).pos ds)
    (by simpa [digitWeights_sum] using hne) (by simpa [digitWeights_sum] using hq),
    weightCoefficient_digits]

include he in
/-- Every nonzero digit monomial of weight at most q−1 has a unit mixed constant. -/
theorem isUnit_mixed_digit_constant (ds : List ℕ) (hds : ∀ d ∈ ds, d < p)
    (hne : Nat.ofDigits p ds ≠ 0) (hq : Nat.ofDigits p ds ≤ Fintype.card Fˣ) :
    IsUnit (mixedConstant ((digitWeights p ds).reverse.map (fun k ↦ χ ^ k))
      (χ ^ Nat.ofDigits p ds)) := by
  let : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  apply (residue_ne_zero_iff_isUnit _).mp
  rw [mixed_digit_constant_residue p χ e he ds hne hq, ← weightCoefficient_digits p ds]
  exact (isUnit_weightCoefficient_digits (R := ResidueField R) p ds hds).ne_zero

end ThreeAdicPlan.CharacterAverage

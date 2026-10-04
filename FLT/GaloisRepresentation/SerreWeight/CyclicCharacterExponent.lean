/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.SerreWeight.NormalizedCharacterExponent

/-!
# Unique exponents for finite cyclic character quotients

The exponent is normalized in `[0, card C)`. This works for higher-niveau
roots of unity as well as prime-field units. Kernel containment remains an
explicit input; no ramification classification is inferred from it.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.SerreWeight

variable {G C : Type*} [Group G] [CommGroup C] [Finite C] [IsCyclic C]
  (θ χ : G →* C) (hθ : Function.Surjective θ) (hker : θ.ker ≤ χ.ker)

include hθ hker

/-- A character on a finite cyclic quotient has exactly one reduced exponent. -/
theorem existsUnique_cyclic_character_exponent :
    ∃! n : ℕ, n < Nat.card C ∧ ∀ g, χ g = θ g ^ n := by
  let := Fintype.ofFinite C
  let ψ := θ.liftOfSurjective hθ ⟨χ, hker⟩
  obtain ⟨a, ha⟩ := cyclicEndomorphism_eq_pow ψ
  have he (g : G) : χ g = θ g ^ a := by simpa [ψ] using ha (θ g)
  refine ⟨a % Nat.card C, ⟨Nat.mod_lt _ Nat.card_pos, fun g ↦ ?_⟩, ?_⟩
  · simpa only [Nat.card_eq_fintype_card] using (he g).trans (pow_mod_card (θ g) a).symm
  · intro b hb
    obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := C)
    obtain ⟨g, hg⟩ := hθ u
    apply pow_injOn_Iio_orderOf (x := u)
      (by simpa [hu] using hb.1) (by simpa [hu] using Nat.mod_lt a (Nat.card_pos (α := C)))
    change u ^ b = u ^ (a % Nat.card C)
    rw [← hg, ← hb.2 g, he]
    exact (by simpa only [Nat.card_eq_fintype_card] using (pow_mod_card (θ g) a).symm)

/-- The reduced exponent is selected from a uniqueness theorem. -/
def cyclicCharacterExponent : ℕ :=
  (existsUnique_cyclic_character_exponent θ χ hθ hker).choose

/-- The extracted exponent recovers the whole character. -/
theorem cyclicCharacterExponent_spec :
    cyclicCharacterExponent θ χ hθ hker < Nat.card C ∧
      ∀ g, χ g = θ g ^ cyclicCharacterExponent θ χ hθ hker :=
  (existsUnique_cyclic_character_exponent θ χ hθ hker).choose_spec.1

/-- Any independently computed reduced exponent agrees with the selected one. -/
theorem cyclicCharacterExponent_eq {n : ℕ} (hn : n < Nat.card C)
    (he : ∀ g, χ g = θ g ^ n) : cyclicCharacterExponent θ χ hθ hker = n :=
  ((existsUnique_cyclic_character_exponent θ χ hθ hker).choose_spec.2 n ⟨hn, he⟩).symm

/-- Changing a surjective normalization by a power transforms exponents modulo the order. -/
theorem cyclicCharacterExponent_change_generator (θ' : G →* C)
    (hθ' : Function.Surjective θ') (hker' : θ'.ker ≤ χ.ker)
    (a : ℕ) (ha : ∀ g, θ' g = θ g ^ a) :
    cyclicCharacterExponent θ χ hθ hker =
      (a * cyclicCharacterExponent θ' χ hθ' hker') % Nat.card C := by
  let := Fintype.ofFinite C
  apply cyclicCharacterExponent_eq θ χ hθ hker (Nat.mod_lt _ Nat.card_pos)
  intro g
  rw [(cyclicCharacterExponent_spec θ' χ hθ' hker').2 g, ha, ← pow_mul]
  symm
  exact (by simpa only [Nat.card_eq_fintype_card] using pow_mod_card (θ g) _)

end GaloisRepresentation.SerreWeight

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudMixedDigitUnit

/-!
# Every integral character is a fundamental power

The constructed faithful character has q−1 distinct positive powers.
The independently proved character duality counts all characters, so
these powers exhaust them, including the trivial character at q−1.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing CharacterAverage

variable {R F : Type} [CommRing R] [IsDomain R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)] [Field F] [Fintype F] [DecidableEq F]
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p] (e : F →+* ResidueField R)

/-- The positive powers of the fundamental character are pairwise distinct up to q−1. -/
theorem fundamentalCharacter_power_injective {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmq : m ≤ Fintype.card Fˣ) (hnq : n ≤ Fintype.card Fˣ)
    (h : fundamentalCharacter p e ^ m = fundamentalCharacter p e ^ n) : m = n := by
  have hr := congrArg (mapCharacter (residue R)) h
  simp only [map_character_power (fundamentalCharacter p e) e
    (fundamentalCharacter_residue p e)] at hr
  exact embeddingCharacter_pow_injective e hm hn hmq hnq hr

/-- All actual integral characters are positive fundamental powers in the canonical range. -/
theorem exists_fundamentalCharacter_power (ψ : Fˣ →* Rˣ) :
    ∃ n : ℕ, 0 < n ∧ n ≤ Fintype.card Fˣ ∧ fundamentalCharacter p e ^ n = ψ := by
  classical
  obtain ⟨_, _, ⟨eqv⟩⟩ := henselian_group_characters (R := R) Fˣ (by
    rw [scalar_units_card_residue (F := F) p]; exact neg_ne_zero.mpr one_ne_zero)
  let : Fintype (Fˣ →* Rˣ) := Fintype.ofEquiv Fˣ eqv.symm.toEquiv
  let f : Fin (Fintype.card Fˣ) → (Fˣ →* Rˣ) :=
    fun n ↦ fundamentalCharacter p e ^ (n.val + 1)
  have hinj : Function.Injective f := by
    intro a b h
    apply Fin.ext
    have heq := fundamentalCharacter_power_injective p e (by omega) (by omega)
      (by omega : a.val + 1 ≤ Fintype.card Fˣ)
      (by omega : b.val + 1 ≤ Fintype.card Fˣ) h
    omega
  have hcard : Fintype.card (Fin (Fintype.card Fˣ)) = Fintype.card (Fˣ →* Rˣ) := by
    rw [Fintype.card_fin, Fintype.card_congr eqv.toEquiv]
  obtain ⟨n, hn⟩ := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩).surjective ψ
  exact ⟨n.val + 1, by omega, by omega, hn⟩

end ThreeAdicPlan

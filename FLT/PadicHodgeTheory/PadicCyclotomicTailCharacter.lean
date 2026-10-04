/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicCyclotomicTailAutomorphism
public import FLT.AbsoluteGaloisGroup.CyclotomicCharacterNaturality

/-! # Every nonzero weight is detected above every finite cyclotomic level -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [hp : Fact p.Prime]

/-- No positive character power is trivial on a cyclotomic tail Galois group. -/
theorem padicCyclotomic_tail_character_pow_ne_one (n k : ℕ) (hk : k ≠ 0) :
    ∃ σ : Gal(PadicAlgCl p/padicCyclotomicTower p (n + 1)),
      cyclotomicCharacter (PadicAlgCl p) p (σ.restrictScalars ℚ_[p]).toRingEquiv ^ k ≠ 1 := by
  let a := 1 + p ^ (n + 1)
  let r := a ^ k
  have ha : 1 < a := by dsimp [a]; have := pow_pos hp.out.pos (n + 1); omega
  have hsmall : a ^ k < p ^ (n + r + 1) := by
    have hpow : r < p ^ r := Nat.lt_pow_self hp.out.one_lt
    exact hpow.trans_le (Nat.pow_le_pow_right hp.out.pos (by omega))
  have haPow : a ≤ a ^ k := le_self_pow₀ ha.le hk
  have haSmall : a < p ^ (n + r + 1) := haPow.trans_lt hsmall
  have hmod : 1 < p ^ (n + r + 1) := ha.trans haSmall
  let : NeZero (p ^ (n + r + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ (n + r + 1))
  obtain ⟨σ, hσ⟩ := padicCyclotomic_exists_tail_automorphism p n r ζ hζ
  refine ⟨σ, fun hχ ↦ ?_⟩
  let χ := cyclotomicCharacter (PadicAlgCl p) p (σ.restrictScalars ℚ_[p]).toRingEquiv
  have hs := cyclotomicCharacter.spec p (σ.restrictScalars ℚ_[p]).toRingEquiv ζ hζ.pow_eq_one
  have hc : χ.val.toZModPow (n + r + 1) = (a : ZMod (p ^ (n + r + 1))) := by
    apply ZMod.val_injective
    rw [ZMod.val_natCast_of_lt haSmall]
    apply hζ.pow_inj (ZMod.val_lt _) haSmall
    exact hs.symm.trans hσ
  have hz := congrArg (fun u : ℤ_[p]ˣ ↦ u.val.toZModPow (n + r + 1)) hχ
  change (χ ^ k).val.toZModPow (n + r + 1) = (1 : ℤ_[p]ˣ).val.toZModPow (n + r + 1) at hz
  rw [Units.val_pow_eq_pow_val, map_pow, hc, Units.val_one, map_one, ← Nat.cast_pow] at hz
  have hv := congrArg ZMod.val hz
  rw [ZMod.val_natCast_of_lt hsmall, ZMod.val_one'' hmod.ne'] at hv
  exact (ne_of_gt (one_lt_pow₀ ha hk)) hv

/-- Every nonzero integral character weight is detected on every cyclotomic tail. -/
theorem padicCyclotomic_tail_character_zpow_ne_one (n : ℕ) (k : ℤ) (hk : k ≠ 0) :
    ∃ σ : Gal(PadicAlgCl p/padicCyclotomicTower p (n + 1)),
      cyclotomicCharacter (PadicAlgCl p) p (σ.restrictScalars ℚ_[p]).toRingEquiv ^ k ≠ 1 := by
  obtain ⟨σ, hσ⟩ := padicCyclotomic_tail_character_pow_ne_one p n k.natAbs
    (Int.natAbs_ne_zero.mpr hk)
  exact ⟨σ, fun h ↦ hσ (pow_natAbs_eq_one.mpr h)⟩

end PadicHodgeTheory

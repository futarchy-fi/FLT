/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicCyclotomicUniformTrace
public import FLT.AbsoluteGaloisGroup.CyclotomicCharacterNaturality

/-! # The character kernel fixes precisely the cyclotomic union -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [hp : Fact p.Prime]

/-- Character-kernel automorphisms fix all actual cyclotomic roots. -/
theorem padicCyclotomic_kernel_fixes_root (σ : PadicGalois p)
    (hσ : cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv = 1)
    (n : ℕ) (ζ : PadicAlgCl p) (hζ : ζ ^ (p ^ n) = 1) : σ ζ = ζ := by
  have h := cyclotomicCharacter.spec p σ.toRingEquiv ζ hζ
  rw [hσ, Units.val_one, map_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ,
    pow_one] at h
  exact h

/-- The character kernel fixes every element of the actual cyclotomic union. -/
theorem padicCyclotomic_kernel_fixes_union (σ : PadicGalois p)
    (hσ : cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv = 1)
    (x : padicCyclotomicUnion p) : σ (x : PadicAlgCl p) = x := by
  obtain ⟨n, hn⟩ := (mem_padicCyclotomicUnion p x).mp x.property
  change (x : PadicAlgCl p) ∈ IntermediateField.adjoin ℚ_[p] _ at hn
  refine IntermediateField.adjoin_induction ℚ_[p] (p := fun y _ ↦ σ y = y)
    ?_ (fun a ↦ σ.commutes a) ?_ ?_ ?_ hn
  · rintro ζ ⟨k, hk, _, hζ⟩
    obtain rfl : k = p ^ (n + 1) := hk
    exact padicCyclotomic_kernel_fixes_root p σ hσ (n + 1) ζ hζ
  · intro a b _ _ ha hb; rw [map_add, ha, hb]
  · intro a _ ha; rw [map_inv₀, ha]
  · intro a b _ _ ha hb; rw [map_mul, ha, hb]

/-- Fixing the actual union forces the entire p-adic character to be one. -/
theorem padicCyclotomic_character_eq_one_of_fixes_union (σ : PadicGalois p)
    (hσ : ∀ x : padicCyclotomicUnion p, σ (x : PadicAlgCl p) = x) :
    cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv = 1 := by
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  by_cases hn : n = 0
  · subst n
    have : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  have hp1 : 1 < p ^ n := one_lt_pow₀ hp.out.one_lt hn
  let : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ n)
  have hm : ζ ∈ padicCyclotomicUnion p := by
    apply (mem_padicCyclotomicUnion p ζ).mpr
    exact ⟨n, padicCyclotomicTower_mono p (Nat.le_succ n)
      (padicCyclotomicTower_root_mem p n ζ hζ.pow_eq_one)⟩
  have hs := cyclotomicCharacter.spec p σ.toRingEquiv ζ hζ.pow_eq_one
  change σ ζ = _ at hs
  rw [hσ ⟨ζ, hm⟩] at hs
  apply ZMod.val_injective
  rw [Units.val_one, map_one, ZMod.val_one'' hp1.ne']
  apply hζ.pow_inj (ZMod.val_lt _) hp1
  simpa only [pow_one] using hs.symm

/-- The kernel is exactly the fixing subgroup of the actual root-generated union. -/
theorem padicCyclotomic_kernel_iff_fixes_union (σ : PadicGalois p) :
    cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv = 1 ↔
      ∀ x : padicCyclotomicUnion p, σ (x : PadicAlgCl p) = x :=
  ⟨padicCyclotomic_kernel_fixes_union p σ,
    padicCyclotomic_character_eq_one_of_fixes_union p σ⟩

end PadicHodgeTheory

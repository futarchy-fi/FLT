/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.RepresentationTheory.SmallQuotient

/-!
# Characters with a normal three-subgroup and quotient of order two

Every character to the units of `ZMod 3` kills a three-subgroup. If the
quotient has order two, any fixed nontrivial character is the unique
nontrivial character.
-/

@[expose] public noncomputable section

namespace Representation

/-- A character into the units of `ZMod 3` kills every three-subgroup. -/
theorem threeSubgroup_le_character_ker {G : Type*} [Group G]
    (P : Subgroup G) (hP : IsPGroup 3 P) (χ : G →* (ZMod 3)ˣ) : P ≤ χ.ker := by
  intro x hx
  obtain ⟨y, hy⟩ := (hP.powEquiv (by decide : Nat.Coprime 3 2)).surjective ⟨x, hx⟩
  have hxy : (y : G) ^ 2 = x := congrArg Subtype.val hy
  rw [MonoidHom.mem_ker, ← hxy, map_pow]
  exact (by decide : ∀ u : (ZMod 3)ˣ, u ^ 2 = 1) _

/-- On a group of order two every character is trivial or equals a specified
nontrivial character. -/
theorem character_eq_one_or_eq_of_card_two {G : Type*} [Group G]
    (hG : Nat.card G = 2) (ε χ : G →* (ZMod 3)ˣ) (hε : ε ≠ 1) : χ = 1 ∨ χ = ε := by
  obtain ⟨a, ha, huniq⟩ := (Nat.card_eq_two_iff' (1 : G)).mp hG
  have hεa : ε a ≠ 1 := by
    intro h
    apply hε
    apply MonoidHom.ext
    intro g
    by_cases hg : g = 1
    · simp [hg]
    · rw [huniq g hg, h, MonoidHom.one_apply]
  have hεneg : ε a = -1 :=
    ((by decide : ∀ u : (ZMod 3)ˣ, u = 1 ∨ u = -1) (ε a)).resolve_left hεa
  rcases (by decide : ∀ u : (ZMod 3)ˣ, u = 1 ∨ u = -1) (χ a) with hχ | hχ
  · left
    apply MonoidHom.ext
    intro g
    by_cases hg : g = 1
    · simp [hg]
    · rw [huniq g hg, hχ, MonoidHom.one_apply]
  · right
    apply MonoidHom.ext
    intro g
    by_cases hg : g = 1
    · simp [hg]
    · rw [huniq g hg, hχ, hεneg]

/-- A normal three-subgroup with quotient of order two leaves exactly the
trivial character and any specified nontrivial character. -/
theorem character_eq_one_or_eq_of_normal_threeSubgroup
    {G : Type*} [Group G] (P : Subgroup G) [P.Normal] (hP : IsPGroup 3 P)
    (hcard : Nat.card (G ⧸ P) = 2) (ε χ : G →* (ZMod 3)ˣ) (hε : ε ≠ 1) :
    χ = 1 ∨ χ = ε := by
  let ε' := QuotientGroup.lift P ε (threeSubgroup_le_character_ker P hP ε)
  let χ' := QuotientGroup.lift P χ (threeSubgroup_le_character_ker P hP χ)
  have hε' : ε' ≠ 1 := by
    intro h
    apply hε
    apply MonoidHom.ext
    intro g
    exact congrArg (fun f : G ⧸ P →* (ZMod 3)ˣ ↦ f (QuotientGroup.mk' P g)) h
  rcases character_eq_one_or_eq_of_card_two hcard ε' χ' hε' with h | h
  · left
    apply MonoidHom.ext
    intro g
    exact congrArg (fun f : G ⧸ P →* (ZMod 3)ˣ ↦ f (QuotientGroup.mk' P g)) h
  · right
    apply MonoidHom.ext
    intro g
    exact congrArg (fun f : G ⧸ P →* (ZMod 3)ˣ ↦ f (QuotientGroup.mk' P g)) h

end Representation

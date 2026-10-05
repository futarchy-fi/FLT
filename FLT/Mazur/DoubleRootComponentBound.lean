/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fin.VecNotation

/-!
# A four-element bound from a simple class and an opposite pair

A nonzero element lies either in a class where all elements agree, or in
a class where all elements agree up to sign. These comparisons bound the
whole group by four, without assuming that either class is inhabited.
-/

@[expose] public section

namespace FLT.Mazur

/-- One simple class and one pair of opposite classes bound a group by four. -/
theorem finite_card_le_four_of_simple_or_opposite {G : Type*} [AddGroup G]
    (S D : G → Prop) (hc : ∀ c : G, c ≠ 0 → S c ∨ D c)
    (hs : ∀ c d : G, S c → S d → c = d)
    (hd : ∀ c d : G, D c → D d → c = d ∨ c = -d) :
    Finite G ∧ Nat.card G ≤ 4 := by
  classical
  have hexS : ∃ s : G, ∀ c : G, S c → c = s := by
    by_cases he : ∃ s, S s
    · obtain ⟨s, hs'⟩ := he
      exact ⟨s, fun c hc' => hs c s hc' hs'⟩
    · exact ⟨0, fun c hc' => False.elim (he ⟨c, hc'⟩)⟩
  have hexD : ∃ d : G, ∀ c : G, D c → c = d ∨ c = -d := by
    by_cases he : ∃ d, D d
    · obtain ⟨d, hd'⟩ := he
      exact ⟨d, fun c hc' => hd c d hc' hd'⟩
    · exact ⟨0, fun c hc' => False.elim (he ⟨c, hc'⟩)⟩
  obtain ⟨s, hs'⟩ := hexS
  obtain ⟨d, hd'⟩ := hexD
  let f : Fin 4 → G := ![0, s, d, -d]
  have hf : Function.Surjective f := by
    intro c
    by_cases hz : c = 0
    · exact ⟨0, hz.symm⟩
    · rcases hc c hz with h | h
      · exact ⟨1, (hs' c h).symm⟩
      · rcases hd' c h with he | he
        · exact ⟨2, he.symm⟩
        · exact ⟨3, he.symm⟩
  exact ⟨Finite.of_surjective f hf, by simpa using Nat.card_le_card_of_surjective f hf⟩

end FLT.Mazur

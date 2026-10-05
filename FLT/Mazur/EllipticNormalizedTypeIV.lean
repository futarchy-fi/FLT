/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticTypeIVComponentComparison
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The normalized type IV rational component bound

Under the additive coefficient tests and exact depth two of b₆, the actual
quotient E/E₀ is finite of order at most three. All coefficient factors are
constructed from a generator of the maximal ideal; no component labels or
classification are assumed.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- A group whose nonzero elements are pairwise equal or opposite has at most three elements. -/
theorem finite_card_le_three_of_eq_or_neg {G : Type*} [AddGroup G]
    (h : ∀ c d : G, c ≠ 0 → d ≠ 0 → c = d ∨ c = -d) :
    Finite G ∧ Nat.card G ≤ 3 := by
  classical
  have hex : ∃ c : G, ∀ d : G, d = 0 ∨ d = c ∨ d = -c := by
    by_cases hn : ∃ c : G, c ≠ 0
    · obtain ⟨c, hc⟩ := hn
      refine ⟨c, fun d => ?_⟩
      by_cases hd : d = 0
      · exact Or.inl hd
      · exact Or.inr (h d c hd hc)
    · push Not at hn
      exact ⟨0, fun d => Or.inl (hn d)⟩
  obtain ⟨c, hc⟩ := hex
  let f : Fin 3 → G := ![0, c, -c]
  have hf : Function.Surjective f := by
    intro d
    rcases hc d with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  exact ⟨Finite.of_surjective f hf, by simpa using Nat.card_le_card_of_surjective f hf⟩

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  {π : A} (hπ : π ≠ 0) (hgen : maximalIdeal A = Ideal.span {π})
  (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A)
  (h3 : W.a₃ ∈ maximalIdeal A) (h4 : W.a₄ ∈ maximalIdeal A ^ 2)
  (h6 : W.a₆ ∈ maximalIdeal A ^ 2) (hb6 : W.b₆ ∉ maximalIdeal A ^ 3)

include hπ hgen h1 h2 h3 h4 h6 hb6

/-- Every two nonzero actual components are equal or opposite under the type IV tests. -/
theorem component_eq_or_neg_of_normalizedTypeIV (c d : EllipticComponentQuotient A W)
    (hc : c ≠ 0) (hd : d ≠ 0) : c = d ∨ c = -d := by
  have h4m := Ideal.pow_le_self (by decide : 2 ≠ 0) h4
  have h6m := Ideal.pow_le_self (by decide : 2 ≠ 0) h6
  obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A W c
  obtain ⟨Q, rfl⟩ := ellipticComponentHom_surjective A W d
  obtain ⟨v⟩ := exists_typeIVCoordinates A W π hgen h3 h4m h6m P
    (fun h => hc ((ellipticComponentHom_eq_zero A W P).mpr h))
  obtain ⟨w⟩ := exists_typeIVCoordinates A W π hgen h3 h4m h6m Q
    (fun h => hd ((ellipticComponentHom_eq_zero A W Q).mpr h))
  obtain ⟨e3, he3⟩ := exists_node_coordinate_factor hgen 1 (by simpa using h3)
  obtain ⟨e4, he4m, he4⟩ := exists_node_deep_factor hgen 1 h4
  obtain ⟨e6, he6⟩ := exists_node_coordinate_factor hgen 2 h6
  exact v.component_eq_or_neg w hπ (hgen ▸ Ideal.mem_span_singleton_self π)
    e3 e4 e6 h1 h2 he4m (by simpa using he3) (by simpa using he4) he6 hb6

/-- The normalized type IV quotient is finite and has at most three elements. -/
theorem normalizedTypeIV_components :
    Finite (EllipticComponentQuotient A W) ∧ Nat.card (EllipticComponentQuotient A W) ≤ 3 :=
  finite_card_le_three_of_eq_or_neg
    (component_eq_or_neg_of_normalizedTypeIV A W hπ hgen h1 h2 h3 h4 h6 hb6)

end FLT.Mazur

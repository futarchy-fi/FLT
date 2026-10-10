/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginPoleSums

/-!
# Exact pole bounds for sums with distinct weights

Peeling off a largest weight proves that every coefficient above the allowed
pole order vanishes. This is valid over arbitrary rings, without passing to
geometric points or discarding nilpotents.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Distinct monomial weights cannot cancel in the original pole filtration. -/
theorem originPole_sum_monomials_iff (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → R)
    (hsep : Set.InjOn (fun k : ℕ × ℕ ↦ 2 * k.1 + 3 * k.2) s) (n : ℕ) :
    HasOriginPoleBound W (∑ k ∈ s, originPoleMonomial W (c k) k.1 k.2) n ↔
      ∀ k ∈ s, c k = 0 ∨ 2 * k.1 + 3 * k.2 ≤ n := by
  classical
  induction s using Finset.induction_on_max_value (fun k : ℕ × ℕ ↦ 2 * k.1 + 3 * k.2)
      generalizing n with
  | empty => simp [originPole_zero]
  | insert a s ha hmax ih =>
    have hsep' : Set.InjOn (fun k : ℕ × ℕ ↦ 2 * k.1 + 3 * k.2) s :=
      hsep.mono (by intro k hk; exact Finset.mem_insert_of_mem hk)
    have hlt (k : ℕ × ℕ) (hk : k ∈ s) : 2 * k.1 + 3 * k.2 < 2 * a.1 + 3 * a.2 := by
      apply lt_of_le_of_ne (hmax k hk)
      intro he
      have hka := hsep (Finset.mem_insert_of_mem hk) (Finset.mem_insert_self a s) he
      exact ha (hka ▸ hk)
    rw [Finset.sum_insert ha]
    constructor
    · intro h
      by_cases han : 2 * a.1 + 3 * a.2 ≤ n
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact Or.inr han
        · exact Or.inr ((hmax k hk).trans han)
      · have hb : HasOriginPoleBound W
            (∑ k ∈ s, originPoleMonomial W (c k) k.1 k.2)
            (2 * a.1 + 3 * a.2 - 1) := by
          apply originPole_sum
          intro k hk
          exact originPole_mono W _ (by have := hlt k hk; omega)
            (originPoleMonomial_bound W (c k) k.1 k.2)
        have hc := originPoleMonomial_add_lower W (c a) a.1 a.2 n _
          (Nat.lt_of_not_ge han) hb h
        have hz : originPoleMonomial W (c a) a.1 a.2 = 0 := by
          simp [originPoleMonomial, hc]
        rw [hz, zero_add] at h
        have hs := (ih hsep' n).mp h
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact Or.inl hc
        · exact hs k hk
    · intro h
      apply originPole_add
      · exact (originPoleMonomial_bound_iff W _ _ _ _).mpr
          (h a (Finset.mem_insert_self a s))
      · exact (ih hsep' n).mpr (fun k hk ↦ h k (Finset.mem_insert_of_mem hk))

/-- The weights of normal-form monomials are distinct: their y exponents are zero or one. -/
theorem originNormalWeight_injective {s : Finset (ℕ × ℕ)}
    (hs : ∀ k ∈ s, k.2 ≤ 1) :
    Set.InjOn (fun k : ℕ × ℕ ↦ 2 * k.1 + 3 * k.2) s := by
  intro a ha b hb he
  change 2 * a.1 + 3 * a.2 = 2 * b.1 + 3 * b.2 at he
  have hya := hs a ha
  have hyb := hs b hb
  apply Prod.ext <;> omega

end FLT.Mazur.WeierstrassIntegralChart

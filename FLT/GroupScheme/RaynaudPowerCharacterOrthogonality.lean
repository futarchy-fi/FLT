/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterOrthogonality
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Orthogonality for powers of an embedding character

Positive exponents up to the order of the multiplicative group give all
distinct power characters. Their normalized pairings are Kronecker deltas.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CharacterAverage

variable {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Fintype Fˣ]
  (e : F →+* R)

/-- The multiplicative character of a field embedding. -/
def embeddingCharacter : Fˣ →* Rˣ := Units.map e.toMonoidHom

omit [Fintype Fˣ] in
/-- The embedding character is faithful. -/
theorem embeddingCharacter_injective : Function.Injective (embeddingCharacter e) := by
  intro a b h
  apply Units.ext
  exact e.injective (congrArg Units.val h)

/-- Positive exponents up to the group order distinguish power characters. -/
theorem embeddingCharacter_pow_injective {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmq : m ≤ Fintype.card Fˣ) (hnq : n ≤ Fintype.card Fˣ)
    (h : embeddingCharacter e ^ m = embeddingCharacter e ^ n) : m = n := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have ho : orderOf (embeddingCharacter e g) = Fintype.card Fˣ := by
    rw [orderOf_injective _ (embeddingCharacter_injective e), hg, Nat.card_eq_fintype_card]
  have heq : embeddingCharacter e g ^ m = embeddingCharacter e g ^ n :=
    congrArg (fun c : Fˣ →* Rˣ ↦ c g) h
  have hs : embeddingCharacter e g ^ (m - 1) = embeddingCharacter e g ^ (n - 1) := by
    apply mul_right_cancel (b := embeddingCharacter e g)
    simpa only [← pow_succ, Nat.sub_add_cancel hm, Nat.sub_add_cancel hn] using heq
  have := pow_injOn_Iio_orderOf (x := embeddingCharacter e g)
    (show m - 1 < orderOf (embeddingCharacter e g) by rw [ho]; omega)
    (show n - 1 < orderOf (embeddingCharacter e g) by rw [ho]; omega) hs
  omega

variable [Invertible (Fintype.card Fˣ : R)]

/-- Normalized character ratios sum to one on the diagonal and zero off it. -/
theorem embedding_power_average (k j : ℕ) (hk : 0 < k) (hj : 0 < j)
    (hkq : k ≤ Fintype.card Fˣ) (hjq : j ≤ Fintype.card Fˣ) :
    ⅟(Fintype.card Fˣ : R) * ∑ u : Fˣ,
      (↑((embeddingCharacter e ^ k) u)⁻¹ : R) * e u ^ j = if k = j then 1 else 0 := by
  classical
  by_cases h : k = j
  · subst j
    simp only [MonoidHom.pow_apply, embeddingCharacter]
    have hi (u : Fˣ) : (↑((Units.map e.toMonoidHom u ^ k)⁻¹) : R) * e u ^ k = 1 := by
      exact Units.inv_mul (Units.map e.toMonoidHom u ^ k)
    simp only [hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      invOf_mul_self, ite_true]
  · rw [ite_eq_right h]
    have hc : (embeddingCharacter e ^ k)⁻¹ * embeddingCharacter e ^ j ≠ 1 := by
      intro heq
      exact h (embeddingCharacter_pow_injective e hk hj hkq hjq (inv_mul_eq_one.mp heq))
    have hs := CharacterProjector.sum_character_eq_zero
      ((embeddingCharacter e ^ k)⁻¹ * embeddingCharacter e ^ j) hc
    have hs' : ∑ u : Fˣ,
        (↑((embeddingCharacter e ^ k) u)⁻¹ : R) * e u ^ j = 0 := by
      exact hs
    rw [hs', mul_zero]

end ThreeAdicPlan.CharacterAverage

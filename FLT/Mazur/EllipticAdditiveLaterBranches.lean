/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticAdditiveStarTranslation
public import FLT.Mazur.EllipticTripleRootBranches

/-!
# The remaining additive alternatives after the triple-root branches

Starting with all coefficients in m, the actual quotient is bounded by
four, or an integral translation produces one of two explicit models:
the double-root branch (a₂ of exact depth one), or weighted scaling depths
(1,2,3,4,6). The Iₙ* iteration and exclusion of the latter alternative by
minimality remain separate tasks.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- The additive tests leave only the double-root iteration or weighted scaling depths. -/
theorem normalizedAdditive_bound_or_double_or_scaling {K : Type*} [Field K]
    (A : ValuationSubring K) (W : WeierstrassCurve A) {π : A} (hπ : π ≠ 0)
    (hgen : maximalIdeal A = Ideal.span {π}) [(W.map (algebraMap A K)).IsElliptic]
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A)
    (h3 : W.a₃ ∈ maximalIdeal A) (h4 : W.a₄ ∈ maximalIdeal A)
    (h6 : W.a₆ ∈ maximalIdeal A) :
    (Finite (EllipticComponentQuotient A W) ∧ Nat.card (EllipticComponentQuotient A W) ≤ 4) ∨
    (∃ r t : A, r ∈ maximalIdeal A ∧ t ∈ maximalIdeal A ∧
      let V := (VariableChange.mk 1 r 0 t : VariableChange A) • W
      V.a₁ ∈ maximalIdeal A ∧ V.a₂ ∈ maximalIdeal A ∧ V.a₂ ∉ maximalIdeal A ^ 2 ∧
      V.a₃ ∈ maximalIdeal A ^ 2 ∧ V.a₄ ∈ maximalIdeal A ^ 3 ∧ V.a₆ = 0) ∨
    ∃ r t : A, r ∈ maximalIdeal A ∧ t ∈ maximalIdeal A ∧
      let V := (VariableChange.mk 1 r 0 t : VariableChange A) • W
      V.a₁ ∈ maximalIdeal A ∧ V.a₂ ∈ maximalIdeal A ^ 2 ∧
      V.a₃ ∈ maximalIdeal A ^ 3 ∧ V.a₄ ∈ maximalIdeal A ^ 4 ∧
      V.a₆ ∈ maximalIdeal A ^ 6 := by
  classical
  rcases normalizedAdditive_bound_or_star_translation A W hπ hgen h1 h2 h3 h4 h6 with
    hb | ⟨r, t, hr, ht, h1', h2', h3', h4', h6'⟩
  · exact Or.inl hb
  · let C : VariableChange A := .mk 1 r 0 t
    let V := C • W
    by_cases h2'' : V.a₂ ∈ maximalIdeal A ^ 2
    · have : (V.map (algebraMap A K)).IsElliptic := by
        dsimp only [V]
        rw [← map_variableChange]
        infer_instance
      have h6m : V.a₆ ∈ maximalIdeal A ^ 4 := h6' ▸ (maximalIdeal A ^ 4).zero_mem
      rcases normalizedTripleRoot_bound_or_scaling_depths A V hπ hgen
          h1' h2'' h3' h4' h6m with ⟨hf, hc⟩ | ⟨s, hs, hV⟩
      · let e := integralComponentVariableChange A W C
        refine Or.inl ⟨Finite.of_equiv _ e.toEquiv, ?_⟩
        rw [← Nat.card_congr e.toEquiv]
        exact hc.trans (by decide)
      · refine Or.inr (Or.inr ⟨r, t + s, hr,
          (maximalIdeal A).add_mem ht (Ideal.pow_le_self (by decide : 2 ≠ 0) hs), ?_⟩)
        have he : (VariableChange.mk 1 0 0 s : VariableChange A) • V =
            (VariableChange.mk 1 r 0 (t + s) : VariableChange A) • W := by
          dsimp only [V, C]
          rw [← mul_smul]
          simp [VariableChange.mul_def, add_comm]
        simpa only [he] using hV
    · exact Or.inr (Or.inl ⟨r, t, hr, ht, h1', h2', h2'', h3', h4', h6'⟩)

end FLT.Mazur

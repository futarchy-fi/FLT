/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticRepeatedCubicTranslation
public import FLT.Mazur.EllipticAdditiveFirstBranches

/-!
# Entering the later additive branches with an actual integral model

The first additive tests either bound the original component quotient by
four, or construct a translation with depths (1,1,2,3) and a₆ = 0. Thus the
remaining double/triple-root analysis starts with an actual isomorphic
model and no assumed rational root of a repeated discriminant.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- The I₀* chart either bounds E/E₀ or supplies a deeper translated model. -/
theorem starZero_bound_or_deeper_translation {π : A} (hπ : π ≠ 0)
    (hgen : maximalIdeal A = Ideal.span {π}) (e1 e2 e3 e4 e6 : A)
    (h1 : W.a₁ = π * e1) (h2 : W.a₂ = π * e2)
    (h3 : W.a₃ = π ^ 2 * e3) (h4 : W.a₄ = π ^ 2 * e4) (h6 : W.a₆ = π ^ 3 * e6) :
    (Finite (EllipticComponentQuotient A W) ∧ Nat.card (EllipticComponentQuotient A W) ≤ 4) ∨
    ∃ r t : A, r ∈ maximalIdeal A ∧ t ∈ maximalIdeal A ^ 2 ∧
      let V := (VariableChange.mk 1 r 0 t : VariableChange A) • W
      V.a₁ ∈ maximalIdeal A ∧ V.a₂ ∈ maximalIdeal A ∧
      V.a₃ ∈ maximalIdeal A ^ 2 ∧ V.a₄ ∈ maximalIdeal A ^ 3 ∧ V.a₆ = 0 := by
  rcases starZero_bound_or_repeated_point A W hπ hgen e1 e2 e3 e4 e6
      h1 h2 h3 h4 h6 with hb | ⟨P, _, v, hd⟩
  · exact Or.inl hb
  · have hm : π ∈ maximalIdeal A := hgen ▸ Ideal.mem_span_singleton_self π
    obtain ⟨ha, hb, hc, hd', he⟩ := repeatedCubic_point_translation_depths W hm
      v.x v.y e1 e2 e3 e4 h1 h2 h3 h4 v.equation hd
    exact Or.inr ⟨π * v.x, π ^ 2 * v.y, (maximalIdeal A).mul_mem_right _ hm,
      (maximalIdeal A ^ 2).mul_mem_right _ (Ideal.pow_mem_pow hm 2), ha,
      hb ▸ (maximalIdeal A).mul_mem_right _ hm, hc, hd', he⟩

/-- All early additive branches reduce to bound four or depths (1,1,2,3) with a₆ zero. -/
theorem normalizedAdditive_bound_or_star_translation {π : A} (hπ : π ≠ 0)
    (hgen : maximalIdeal A = Ideal.span {π}) [(W.map (algebraMap A K)).IsElliptic]
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A)
    (h3 : W.a₃ ∈ maximalIdeal A) (h4 : W.a₄ ∈ maximalIdeal A)
    (h6 : W.a₆ ∈ maximalIdeal A) :
    (Finite (EllipticComponentQuotient A W) ∧ Nat.card (EllipticComponentQuotient A W) ≤ 4) ∨
    ∃ r t : A, r ∈ maximalIdeal A ∧ t ∈ maximalIdeal A ∧
      let V := (VariableChange.mk 1 r 0 t : VariableChange A) • W
      V.a₁ ∈ maximalIdeal A ∧ V.a₂ ∈ maximalIdeal A ∧
      V.a₃ ∈ maximalIdeal A ^ 2 ∧ V.a₄ ∈ maximalIdeal A ^ 3 ∧ V.a₆ = 0 := by
  classical
  rcases normalizedAdditive_bound_or_deep_translation A W hπ hgen h1 h2 h3 h4 h6 with
    ⟨hf, hc⟩ | ⟨t, ht, h1', h2', h3', h4', h6'⟩
  · exact Or.inl ⟨hf, hc.trans (by decide)⟩
  · let C : VariableChange A := .mk 1 0 0 t
    let V := C • W
    obtain ⟨e1, he1⟩ := exists_node_coordinate_factor hgen 1 (by simpa using h1')
    obtain ⟨e2, he2⟩ := exists_node_coordinate_factor hgen 1 (by simpa using h2')
    obtain ⟨e3, he3⟩ := exists_node_coordinate_factor hgen 2 h3'
    obtain ⟨e4, he4⟩ := exists_node_coordinate_factor hgen 2 h4'
    obtain ⟨e6, he6⟩ := exists_node_coordinate_factor hgen 3 h6'
    simp only [pow_one] at he1 he2
    rcases starZero_bound_or_deeper_translation A V hπ hgen e1 e2 e3 e4 e6
        he1 he2 he3 he4 he6 with ⟨hf, hc⟩ | ⟨r, s, hr, hs, hV⟩
    · let e := integralComponentVariableChange A W C
      refine Or.inl ⟨Finite.of_equiv _ e.toEquiv, ?_⟩
      rw [← Nat.card_congr e.toEquiv]
      exact hc
    · refine Or.inr ⟨r, t + s, hr,
        (maximalIdeal A).add_mem ht (Ideal.pow_le_self (by decide : 2 ≠ 0) hs), ?_⟩
      have he : (VariableChange.mk 1 r 0 s : VariableChange A) • V =
          (VariableChange.mk 1 r 0 (t + s) : VariableChange A) • W := by
        dsimp only [V, C]
        rw [← mul_smul]
        simp [VariableChange.mul_def, add_comm]
      simpa only [he] using hV

end FLT.Mazur

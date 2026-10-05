/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNormalizedTypeII
public import FLT.Mazur.EllipticNormalizedTypeIV
public import FLT.Mazur.EllipticNormalizedStarZero
public import FLT.Mazur.EllipticAdditiveTranslationDepth
public import FLT.Mazur.EllipticComponentVariableChange

/-!
# Exhausting the first additive branches

Starting with all coefficients in the maximal ideal, the II/III/IV tests
either bound the actual quotient by three or produce an integral translated
model of depths (1,1,2,2,3). The simple-cubic I₀* test then gives the bound
four. The remaining alternative is explicitly the repeated-cubic case;
the later Iₙ*, IV*, III*, II* branches are not asserted here.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  {π : A} (hπ : π ≠ 0) (hgen : maximalIdeal A = Ideal.span {π})
  (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A)
  (h3 : W.a₃ ∈ maximalIdeal A) (h4 : W.a₄ ∈ maximalIdeal A)
  (h6 : W.a₆ ∈ maximalIdeal A)

include hπ hgen h1 h2 h3 h4 h6

/-- The first three additive branches either bound E/E₀ or supply a deeper integral model. -/
theorem normalizedAdditive_bound_or_deep_translation :
    (Finite (EllipticComponentQuotient A W) ∧ Nat.card (EllipticComponentQuotient A W) ≤ 3) ∨
    ∃ t : A, t ∈ maximalIdeal A ∧
      let V := (VariableChange.mk 1 0 0 t : VariableChange A) • W
      V.a₁ ∈ maximalIdeal A ∧ V.a₂ ∈ maximalIdeal A ∧
      V.a₃ ∈ maximalIdeal A ^ 2 ∧ V.a₄ ∈ maximalIdeal A ^ 2 ∧
      V.a₆ ∈ maximalIdeal A ^ 3 := by
  classical
  by_cases h6' : W.a₆ ∈ maximalIdeal A ^ 2
  · by_cases h8 : W.b₈ ∈ maximalIdeal A ^ 3
    · have h4' := (b8_mem_cube_iff_a4_mem_square W hπ hgen h1 h2 h3 h4 h6').mp h8
      by_cases hb6 : W.b₆ ∈ maximalIdeal A ^ 3
      · by_cases hp : ∃ P, ¬ SmoothReduction A W P
        · obtain ⟨P, hP⟩ := hp
          exact Or.inr (exists_additive_deep_y_translation A W hπ hgen
            h1 h2 h3 h4 h6' h8 hb6 P hP)
        · have hz (c : EllipticComponentQuotient A W) : c = 0 := by
            obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A W c
            apply (ellipticComponentHom_eq_zero A W P).mpr
            by_contra hn
            exact hp ⟨P, hn⟩
          have : Subsingleton (EllipticComponentQuotient A W) :=
            ⟨fun c d => (hz c).trans (hz d).symm⟩
          exact Or.inl ⟨inferInstance, by simp only [Nat.card_unique]; omega⟩
      · exact Or.inl (normalizedTypeIV_components A W hπ hgen h1 h2 h3 h4' h6' hb6)
    · obtain ⟨hf, _, hc⟩ := typeIII_b8_components A W h1 h2 h3 h4 h6' h8
      exact Or.inl ⟨hf, hc.trans (by decide)⟩
  · have := ellipticComponent_subsingleton_of_normalizedTypeII A W h3 h4 h6 h6'
    exact Or.inl ⟨inferInstance, by simp only [Nat.card_unique]; omega⟩

/-- After II, III, IV and I₀*, only an explicitly repeated residual cubic remains. -/
theorem normalizedAdditive_bound_or_repeated_cubic [(W.map (algebraMap A K)).IsElliptic] :
    (Finite (EllipticComponentQuotient A W) ∧ Nat.card (EllipticComponentQuotient A W) ≤ 4) ∨
    ∃ t : A, t ∈ maximalIdeal A ∧ ∃ e1 e2 e3 e4 e6 : A,
      let V := (VariableChange.mk 1 0 0 t : VariableChange A) • W
      V.a₁ = π * e1 ∧ V.a₂ = π * e2 ∧ V.a₃ = π ^ 2 * e3 ∧
      V.a₄ = π ^ 2 * e4 ∧ V.a₆ = π ^ 3 * e6 ∧
      (Cubic.mk 1 (residue A e2) (residue A e4) (residue A e6)).discr = 0 := by
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
    by_cases hd : (Cubic.mk 1 (residue A e2) (residue A e4) (residue A e6)).discr = 0
    · exact Or.inr ⟨t, ht, e1, e2, e3, e4, e6, he1, he2, he3, he4, he6, hd⟩
    · obtain ⟨hf, _, hc⟩ := normalizedStarZero_components A V hπ hgen
        e1 e2 e3 e4 e6 he1 he2 he3 he4 he6 hd
      let e := integralComponentVariableChange A W C
      refine Or.inl ⟨Finite.of_equiv _ e.toEquiv, ?_⟩
      rw [← Nat.card_congr e.toEquiv]
      exact hc

end FLT.Mazur

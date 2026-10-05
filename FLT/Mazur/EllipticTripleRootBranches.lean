/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNormalizedTypeIVStar
public import FLT.Mazur.EllipticNormalizedTypeIIIStar
public import FLT.Mazur.EllipticNormalizedTypeIIStar
public import FLT.Mazur.EllipticStarTranslationDepth
public import FLT.Mazur.EllipticComponentVariableChange

/-!
# Exhausting the normalized triple-root tests

The IV*, III*, II* tests either bound the original quotient by three or
construct a translated integral equation with weighted coefficient depths
(1,2,3,4,6). These are precisely the depths permitting division by π in
the Weierstrass scaling. No minimality assertion is assumed here.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- The later triple-root tests leave only a model admitting integral weighted scaling. -/
theorem normalizedTripleRoot_bound_or_scaling_depths {π : A} (hπ : π ≠ 0)
    (hgen : maximalIdeal A = Ideal.span {π}) [(W.map (algebraMap A K)).IsElliptic]
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A ^ 2)
    (h3 : W.a₃ ∈ maximalIdeal A ^ 2) (h4 : W.a₄ ∈ maximalIdeal A ^ 3)
    (h6 : W.a₆ ∈ maximalIdeal A ^ 4) :
    (Finite (EllipticComponentQuotient A W) ∧ Nat.card (EllipticComponentQuotient A W) ≤ 3) ∨
    ∃ t : A, t ∈ maximalIdeal A ^ 2 ∧
      let V := (VariableChange.mk 1 0 0 t : VariableChange A) • W
      V.a₁ ∈ maximalIdeal A ∧ V.a₂ ∈ maximalIdeal A ^ 2 ∧
      V.a₃ ∈ maximalIdeal A ^ 3 ∧ V.a₄ ∈ maximalIdeal A ^ 4 ∧
      V.a₆ ∈ maximalIdeal A ^ 6 := by
  classical
  by_cases hb6 : W.b₆ ∈ maximalIdeal A ^ 5
  · by_cases hp : ∃ P, ¬ SmoothReduction A W P
    · obtain ⟨P, hP⟩ := hp
      obtain ⟨t, ht, h1', h2', h3', h4', h6'⟩ :=
        exists_star_deep_y_translation A W hπ hgen h1 h2 h3 h4 h6 hb6 P hP
      let C : VariableChange A := .mk 1 0 0 t
      let V := C • W
      let e := integralComponentVariableChange A W C
      have transfer (hf : Finite (EllipticComponentQuotient A V))
          (hc : Nat.card (EllipticComponentQuotient A V) ≤ 3) :
          Finite (EllipticComponentQuotient A W) ∧
            Nat.card (EllipticComponentQuotient A W) ≤ 3 := by
        refine ⟨Finite.of_equiv _ e.toEquiv, ?_⟩
        rw [← Nat.card_congr e.toEquiv]
        exact hc
      by_cases h4'' : V.a₄ ∈ maximalIdeal A ^ 4
      · by_cases h6'' : V.a₆ ∈ maximalIdeal A ^ 6
        · exact Or.inr ⟨t, ht, h1', h2', h3', h4'', h6''⟩
        · have := ellipticComponent_subsingleton_of_normalizedTypeIIStar A V hπ hgen
            h1' h2' h3' h4'' h6' h6''
          exact Or.inl (transfer inferInstance (by simp only [Nat.card_unique]; omega))
      · obtain ⟨hf, _, hc⟩ := normalizedTypeIIIStar_components A V hπ hgen
          h1' h2' h3' h4' h6' h4''
        exact Or.inl (transfer hf (hc.trans (by decide)))
    · have hz (c : EllipticComponentQuotient A W) : c = 0 := by
        obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A W c
        apply (ellipticComponentHom_eq_zero A W P).mpr
        by_contra h
        exact hp ⟨P, h⟩
      have : Subsingleton (EllipticComponentQuotient A W) :=
        ⟨fun c d => (hz c).trans (hz d).symm⟩
      exact Or.inl ⟨inferInstance, by simp only [Nat.card_unique]; omega⟩
  · exact Or.inl (normalizedTypeIVStar_components A W hπ hgen h1 h2 h3 h4 h6 hb6)

end FLT.Mazur

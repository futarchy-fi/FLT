/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CategoryDIntegralModels
public import FLT.GroupScheme.FiniteFlatExtensionQuotientIso
public import FLT.GroupScheme.IntegralSimpleQuotient

/-!
# Integral filtrations with a list of canonical factors

The factors are listed from the final quotient downward. Every step retains
the actual integral extension, including faithful flatness and its torsor.
Recursion through simple quotients produces such a filtration under the
explicit simple-model classification. A list with only one kind of factor
recovers the existing `HasFiltration` interface.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {R : Type} [CommRing R] [Algebra R ℚ]

/-- An integral filtration recording its quotient factors from top to bottom. -/
inductive HasFactorFiltration : FiniteFlatObject R → List (FiniteFlatObject R) → Prop
  /-- A trivial integral model has an empty list of factors. -/
  | zero {H : FiniteFlatObject R} (e : H.model.CoordinateRing ≃ₐ[R] R) :
      HasFactorFiltration H []
  /-- Extend a filtered kernel by one specified integral quotient. -/
  | extension {A H Q : FiniteFlatObject R} {factors : List (FiniteFlatObject R)}
      (E : FiniteFlatExtension A H Q) (hA : HasFactorFiltration A factors) :
      HasFactorFiltration H (Q :: factors)

/-- A factor list consisting of one fixed object yields its integral filtration. -/
theorem HasFactorFiltration.ofAllEqual {H Q : FiniteFlatObject R}
    {factors : List (FiniteFlatObject R)} (h : HasFactorFiltration H factors)
    (heq : ∀ J ∈ factors, J = Q) : HasFiltration H Q := by
  induction h with
  | zero e => exact .zero e
  | @extension A H J factors E hA ih =>
    have hJ : J = Q := heq J (by simp)
    subst J
    exact .extension E (ih (fun J hJ ↦ heq J (by simp [hJ])))

/-- Simple-model classification gives a filtration whose actual integral quotient
factors are precisely the constant-three or cube-root models. -/
theorem canonicalFactorFiltrationExists
    (hclass : ∀ A : FiniteFlatObject ZInvTwo, Simple A → InCategoryD A →
      Nonempty (A.Iso constantThree) ∨ Nonempty (A.Iso muThree))
    (H : FiniteFlatObject ZInvTwo) (hD : InCategoryD H) :
    ∃ factors : List (FiniteFlatObject ZInvTwo), HasFactorFiltration H factors ∧
      ∀ Q ∈ factors, Q = constantThree ∨ Q = muThree := by
  suffices h : ∀ n : ℕ, ∀ J : FiniteFlatObject ZInvTwo, Nat.card J.points = n →
      InCategoryD J → ∃ factors, HasFactorFiltration J factors ∧
        ∀ Q ∈ factors, Q = constantThree ∨ Q = muThree from h _ H rfl hD
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro J hn hJ
    by_cases hz : Subsingleton J.points
    · let subsingletonJ : Subsingleton J.points := hz
      exact ⟨[], .zero J.zeroCoordinatesEquiv, by simp⟩
    · let nontrivialJ : Nontrivial J.points := not_subsingleton_iff_nontrivial.mp hz
      obtain ⟨A, Q, E, hs, hlt⟩ := J.existsSimpleQuotient
      obtain ⟨factors, hA, hfactors⟩ :=
        ih (Nat.card A.points) (hlt.trans_eq hn) A rfl (E.inCategoryDLeft hJ)
      rcases hclass Q hs (E.inCategoryDRight hJ) with he | he
      · refine ⟨constantThree :: factors, .extension (E.transportQuotient he.some) hA, ?_⟩
        intro T hT
        rcases List.mem_cons.mp hT with rfl | hT
        · exact Or.inl rfl
        · exact hfactors T hT
      · refine ⟨muThree :: factors, .extension (E.transportQuotient he.some) hA, ?_⟩
        intro T hT
        rcases List.mem_cons.mp hT with rfl | hT
        · exact Or.inr rfl
        · exact hfactors T hT

/-- Discriminant bounds for simple category-D models produce the canonical
integral factor list, with all arithmetic input visible in the hypothesis. -/
theorem canonicalFactorFiltrationOfDiscriminantBounds
    (hdisc : ∀ A : FiniteFlatObject ZInvTwo, Simple A → InCategoryD A →
      AugmentedDiscriminantBound A)
    (H : FiniteFlatObject ZInvTwo) (hD : InCategoryD H) :
    ∃ factors : List (FiniteFlatObject ZInvTwo), HasFactorFiltration H factors ∧
      ∀ Q ∈ factors, Q = constantThree ∨ Q = muThree :=
  canonicalFactorFiltrationExists
    (fun A hs hA ↦ hs.integral_model_of_discriminantBound hA (hdisc A hs hA)) H hD

end ThreeAdicPlan

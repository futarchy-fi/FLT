/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.IntegralCompositeClosedImmersion
public import FLT.GroupScheme.IntegralCompositeFaithfullyFlat
public import FLT.GroupScheme.IntegralCompositeQuotient
public import FLT.GroupScheme.IntegralQuotientIdentification

/-!
# Composition of integral finite-flat extensions

Nested integral kernels produce two actual integral extensions on the
successive quotient. Their inclusion and projection maps commute with the
original diagram, and both sequences retain faithful flatness and torsor data.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {R : Type} [CommRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    [IsDedekindDomain R] [IsPrincipalIdealRing R]

/-- Compose two integral extensions with the compatible inclusion and quotient formulas. -/
theorem composeIntegralExtensionsCompatible
    {A B C H Q : FiniteFlatObject R}
    (E₁ : FiniteFlatExtension A B C) (E₂ : FiniteFlatExtension B H Q) :
    ∃ T : FiniteFlatObject R, ∃ E : FiniteFlatExtension A H T,
      ∃ F : FiniteFlatExtension C T Q,
        E.inclusion = E₁.inclusion.comp E₂.inclusion ∧
        E₁.quotient.comp F.inclusion = E₂.inclusion.comp E.quotient ∧
        E.quotient.comp F.quotient = E₂.quotient := by
  obtain ⟨T, E, i, q, hi, hc, hq⟩ := existsCompositeIntegralQuotient E₁ E₂
  obtain ⟨hiG, hqG, hexact⟩ := compositeIntegralQuotientPointsExact E₁ E₂ E i q hi hc hq
  have hiO := descendedIntegralInclusionSurjective E₁ E₂ E i hi hc
  have hqO := E₂.factorQuotientFaithfullyFlat E.quotient q hq
  let F := FiniteFlatObject.extensionOfExactMaps i q hiG hiO hqG hexact hqO
  refine ⟨T, E, F, hi, ?_, ?_⟩
  · rw [FiniteFlatObject.extensionOfExactMapsInclusion]
    exact hc
  · rw [FiniteFlatObject.extensionOfExactMapsQuotient]
    exact hq

/-- Nested integral extensions give integral extensions by the inner kernel and
between the two successive quotient models. -/
theorem composeIntegralExtensions
    {A B C H Q : FiniteFlatObject R}
    (E₁ : FiniteFlatExtension A B C) (E₂ : FiniteFlatExtension B H Q) :
    ∃ T : FiniteFlatObject R,
      Nonempty (FiniteFlatExtension A H T) ∧ Nonempty (FiniteFlatExtension C T Q) := by
  obtain ⟨T, E, F, _, _, _⟩ := composeIntegralExtensionsCompatible E₁ E₂
  exact ⟨T, ⟨E⟩, ⟨F⟩⟩

end ThreeAdicPlan

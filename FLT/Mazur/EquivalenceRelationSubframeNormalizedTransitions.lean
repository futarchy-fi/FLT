/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeNormalizedRestriction

/-!
# Exact transition terms for independently chosen target lifts

On a common target refinement, the difference of two normalized transfers is
the normalized transfer of their actual restricted difference. The transition
is additive and has the expected cocycle identity; its vanishing is a separate
condition, not a consequence of agreement on the boundary.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient FiniteGroupOpenRelation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (U : (source p q I o).Opens)
  (hU : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U = U)
  (V : (source p q J o').Opens)
  (hV : ∀ σ, (action e J o' σ).hom ⁻¹ᵁ V = V)
  (h : ∀ ι : J ↪ I, U ≤ subframeMap e o o' ι ⁻¹ᵁ V)
  (hN : IsUnit (Nat.choose (Fintype.card I) (Fintype.card J) : Γ(U.toScheme, ⊤)))
local notation "N" => Nat.choose (Fintype.card I) (Fintype.card J)

/-- Normalization preserves subtraction of independent invariant target sections. -/
theorem subframeNormalizedTransfer_sub
    (v w : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    subframeNormalizedTransfer e o o' U hU V hV h hN (v - w) =
      subframeNormalizedTransfer e o o' U hU V hV h hN v -
        subframeNormalizedTransfer e o o' U hU V hV h hN w := by
  apply Subtype.ext
  apply UnitNaturalDivision.nsmul_injective N hN
  change (N • subframeNormalizedTransfer e o o' U hU V hV h hN (v - w)).val =
    (N • (subframeNormalizedTransfer e o o' U hU V hV h hN v -
      subframeNormalizedTransfer e o o' U hU V hV h hN w)).val
  rw [nsmul_sub, nsmul_subframeNormalizedTransfer, nsmul_subframeNormalizedTransfer,
    nsmul_subframeNormalizedTransfer, map_sub]

/-- A transfer transition is zero exactly when the transfer of the target difference is zero. -/
theorem subframeNormalizedTransfer_eq_iff
    (v w : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    subframeNormalizedTransfer e o o' U hU V hV h hN v =
      subframeNormalizedTransfer e o o' U hU V hV h hN w ↔
        subframeTransfer e o o' U hU V hV h (v - w) = 0 := by
  rw [← sub_eq_zero, ← subframeNormalizedTransfer_sub]
  constructor
  · intro hh
    rw [← nsmul_subframeNormalizedTransfer e o o' U hU V hV h hN, hh, smul_zero]
  · intro hh
    apply Subtype.ext
    apply UnitNaturalDivision.nsmul_injective N hN
    change (N • subframeNormalizedTransfer e o o' U hU V hV h hN (v - w)).val = N • 0
    rw [nsmul_subframeNormalizedTransfer, hh, smul_zero]
    rfl

/-- On three independent lifts the constructed transition terms satisfy the exact cocycle. -/
theorem subframeNormalizedTransfer_transition_cocycle
    (u v w : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    subframeNormalizedTransfer e o o' U hU V hV h hN (u - v) +
      subframeNormalizedTransfer e o o' U hU V hV h hN (v - w) =
        subframeNormalizedTransfer e o o' U hU V hV h hN (u - w) := by
  rw [← subframeNormalizedTransfer_add, sub_add_sub_cancel]

/-- Independent target lifts compare by their actual difference on a common refinement. -/
theorem subframeNormalizedTransfer_independent_targets
    (V₂ V₀ : (source p q J o').Opens)
    (hV₂ : ∀ σ, (action e J o' σ).hom ⁻¹ᵁ V₂ = V₂)
    (hV₀ : ∀ σ, (action e J o' σ).hom ⁻¹ᵁ V₀ = V₀)
    (h₂ : ∀ ι : J ↪ I, U ≤ subframeMap e o o' ι ⁻¹ᵁ V₂)
    (h₀ : ∀ ι : J ↪ I, U ≤ subframeMap e o o' ι ⁻¹ᵁ V₀)
    (h₀₁ : V₀ ≤ V) (h₀₂ : V₀ ≤ V₂)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV))
    (w : invariantCoordinates (restrictedAction (action e J o') V₂ hV₂)) :
    subframeNormalizedTransfer e o o' U hU V hV h hN v -
      subframeNormalizedTransfer e o o' U hU V₂ hV₂ h₂ hN w =
        subframeNormalizedTransfer e o o' U hU V₀ hV₀ h₀ hN
          (invariantRestriction (action e J o') V hV V₀ hV₀ h₀₁ v -
            invariantRestriction (action e J o') V₂ hV₂ V₀ hV₀ h₀₂ w) := by
  rw [subframeNormalizedTransfer_sub,
    subframeNormalizedTransfer_restrict_target e o o' U hU V hV h hN V₀ hV₀ h₀₁ h₀,
    subframeNormalizedTransfer_restrict_target e o o' U hU V₂ hV₂ h₂ hN V₀ hV₀ h₀₂ h₀]

end FLT.Mazur.EquivalenceRelationNormalizedFrames

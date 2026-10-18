/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeNormalizedTransfer
public import FLT.Mazur.EquivalenceRelationSubframeTransferRestriction

/-!
# Normalized transfer under independent chart restrictions

Exact division by the unit degree commutes with restriction of either source
or target. Thus the unscaled construction agrees on overlaps when the target
sections themselves are restrictions of the same section. Agreement of
independently chosen target lifts is not asserted.
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

/-- Restricting the source preserves normalized transfer and any choice of unit proof. -/
theorem subframeNormalizedTransfer_restrict_source
    (U₀ : (source p q I o).Opens)
    (hU₀ : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U₀ = U₀) (h₀ : U₀ ≤ U)
    (hN₀ : IsUnit (N : Γ(U₀.toScheme, ⊤)))
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    invariantRestriction (action e I o) U hU U₀ hU₀ h₀
      (subframeNormalizedTransfer e o o' U hU V hV h hN v) =
        subframeNormalizedTransfer e o o' U₀ hU₀ V hV (fun ι ↦ h₀.trans (h ι)) hN₀ v := by
  apply Subtype.ext
  apply UnitNaturalDivision.nsmul_injective N hN₀
  change (N • invariantRestriction (action e I o) U hU U₀ hU₀ h₀
    (subframeNormalizedTransfer e o o' U hU V hV h hN v)).val =
      (N • subframeNormalizedTransfer e o o' U₀ hU₀ V hV
        (fun ι ↦ h₀.trans (h ι)) hN₀ v).val
  rw [← map_nsmul, nsmul_subframeNormalizedTransfer, nsmul_subframeNormalizedTransfer,
    subframeTransfer_restrict_source]

/-- Target restriction preserves the unscaled section on its actual all-selection domain. -/
theorem subframeNormalizedTransfer_restrict_target
    (V₀ : (source p q J o').Opens)
    (hV₀ : ∀ σ, (action e J o' σ).hom ⁻¹ᵁ V₀ = V₀) (h₀ : V₀ ≤ V)
    (hUV₀ : ∀ ι : J ↪ I, U ≤ subframeMap e o o' ι ⁻¹ᵁ V₀)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    subframeNormalizedTransfer e o o' U hU V₀ hV₀ hUV₀ hN
      (invariantRestriction (action e J o') V hV V₀ hV₀ h₀ v) =
        subframeNormalizedTransfer e o o' U hU V hV h hN v := by
  apply Subtype.ext
  apply UnitNaturalDivision.nsmul_injective N hN
  change (N • subframeNormalizedTransfer e o o' U hU V₀ hV₀ hUV₀ hN
    (invariantRestriction (action e J o') V hV V₀ hV₀ h₀ v)).val =
      (N • subframeNormalizedTransfer e o o' U hU V hV h hN v).val
  rw [nsmul_subframeNormalizedTransfer, nsmul_subframeNormalizedTransfer,
    subframeTransfer_restrict_target]

end FLT.Mazur.EquivalenceRelationNormalizedFrames

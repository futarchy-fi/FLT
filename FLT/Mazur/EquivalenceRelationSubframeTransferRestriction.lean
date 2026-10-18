/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeTransfer
public import FLT.Mazur.FiniteGroupOpenCoefficientRefinement

/-!
# Unordered-subframe transfer commutes with independent open restrictions

Refining either chart commutes with transfer. Thus independently chosen source
neighborhoods inherit the same transfer on overlaps, and a target section may
be replaced by its actual restriction without changing the resulting section.
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

/-- Refining only the larger source chart retains each actual selection. -/
@[reassoc] theorem subframeRefinement_restrict_source
    (U₀ : (source p q I o).Opens) (h₀ : U₀ ≤ U) (ι : J ↪ I) :
    (source p q I o).homOfLE h₀ ≫ subframeRefinementMap e o o' ι U V (h ι) =
      subframeRefinementMap e o o' ι U₀ V (h₀.trans (h ι)) := by
  apply (cancel_mono V.ι).mp
  rw [Category.assoc, subframeRefinementMap_inclusion, ← Category.assoc,
    Scheme.homOfLE_ι, subframeRefinementMap_inclusion]

/-- The invariant transfer restricts to the transfer on every smaller stable source chart. -/
theorem subframeTransfer_restrict_source
    (U₀ : (source p q I o).Opens)
    (hU₀ : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U₀ = U₀) (h₀ : U₀ ≤ U)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    invariantRestriction (action e I o) U hU U₀ hU₀ h₀
      (subframeTransfer e o o' U hU V hV h v) =
        subframeTransfer e o o' U₀ hU₀ V hV (fun ι ↦ h₀.trans (h ι)) v := by
  apply Subtype.ext
  change ((source p q I o).homOfLE h₀).appTop
    (subframeTransferSection e o o' U V hV h v) = _
  unfold subframeTransferSection
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  change ((source p q I o).homOfLE h₀ ≫ subframeRefinementMap e o o'
    (SubframeSelections.embedding a) U V (h (SubframeSelections.embedding a))).appTop
      v.val = _
  rw [subframeRefinement_restrict_source]

/-- Refining the target chart retains the actual selection into its original domain. -/
@[reassoc] theorem subframeRefinement_restrict_target
    (V₀ : (source p q J o').Opens) (h₀ : V₀ ≤ V)
    (hUV₀ : ∀ ι : J ↪ I, U ≤ subframeMap e o o' ι ⁻¹ᵁ V₀) (ι : J ↪ I) :
    subframeRefinementMap e o o' ι U V₀ (hUV₀ ι) ≫ (source p q J o').homOfLE h₀ =
      subframeRefinementMap e o o' ι U V (h ι) := by
  apply (cancel_mono V.ι).mp
  simp only [Category.assoc, Scheme.homOfLE_ι, subframeRefinementMap_inclusion]

/-- Restricting an invariant target section does not change its transfer on the common domain. -/
theorem subframeTransfer_restrict_target
    (V₀ : (source p q J o').Opens)
    (hV₀ : ∀ σ, (action e J o' σ).hom ⁻¹ᵁ V₀ = V₀) (h₀ : V₀ ≤ V)
    (hUV₀ : ∀ ι : J ↪ I, U ≤ subframeMap e o o' ι ⁻¹ᵁ V₀)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    subframeTransfer e o o' U hU V₀ hV₀ hUV₀
      (invariantRestriction (action e J o') V hV V₀ hV₀ h₀ v) =
        subframeTransfer e o o' U hU V hV h v := by
  apply Subtype.ext
  change subframeTransferSection e o o' U V₀ hV₀ hUV₀ _ = _
  unfold subframeTransferSection
  apply Finset.sum_congr rfl
  intro a _
  change (subframeRefinementMap e o o' (SubframeSelections.embedding a) U V₀
    (hUV₀ (SubframeSelections.embedding a)) ≫ (source p q J o').homOfLE h₀).appTop
      v.val = _
  rw [subframeRefinement_restrict_target e o o' U V h V₀ h₀ hUV₀]

end FLT.Mazur.EquivalenceRelationNormalizedFrames

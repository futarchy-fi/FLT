/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeNormalizedCorrection

/-!
# Selection errors vanish for equal-size frames

Every embedding between equally sized finite label sets is onto. Thus all
selections have the same image, and target invariance identifies their actual
pullbacks. This proves the original selection errors vanish without a unit or
boundary hypothesis; strict subframes still require a separate argument.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
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
local notation "N" => Nat.choose (Fintype.card I) (Fintype.card J)

/-- Equal cardinalities force every selected pullback of an invariant section to agree. -/
theorem subframePullback_eq_of_card_eq (hc : Fintype.card I = Fintype.card J)
    (ι κ : J ↪ I)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    (subframeRefinementMap e o o' ι U V (h ι)).appTop v.val =
      (subframeRefinementMap e o o' κ U V (h κ)).appTop v.val := by
  apply subframePullback_eq_of_range e o o' U V hV h ι κ _ v
  have hi := (Fintype.bijective_iff_injective_and_card ι).mpr ⟨ι.injective, hc.symm⟩
  have hk := (Fintype.bijective_iff_injective_and_card κ).mpr ⟨κ.injective, hc.symm⟩
  rw [Set.range_eq_univ.mpr hi.surjective, Set.range_eq_univ.mpr hk.surjective]

/-- Equal-size transfer errors vanish on the whole original source chart. -/
theorem subframeTransferSelectionError_eq_zero_of_card_eq
    (hc : Fintype.card I = Fintype.card J) (ι : J ↪ I)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    subframeTransferSelectionError e o o' U V hV h ι v = 0 := by
  apply sub_eq_zero.mpr
  exact subframeTransferSection_of_agreement e o o' U V hV h v _
    (fun κ ↦ subframePullback_eq_of_card_eq e o o' U V hV h hc κ ι v)

/-- Normalized equal-size transfer is each actual selected pullback. -/
theorem subframeNormalizedTransfer_eq_of_card_eq
    (hc : Fintype.card I = Fintype.card J)
    (hN : IsUnit (N : Γ(U.toScheme, ⊤))) (ι : J ↪ I)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    (subframeNormalizedTransfer e o o' U hU V hV h hN v).val =
      (subframeRefinementMap e o o' ι U V (h ι)).appTop v.val :=
  (subframeNormalizedTransfer_selection_iff e o o' U hU V hV h hN ι v).mpr
    (subframeTransferSelectionError_eq_zero_of_card_eq e o o' U V hV h hc ι v)

variable [Etale p]
open MixedFrames

/-- Equal-size normalized transfer solves every original embedding branch. -/
theorem subframeNormalizedTransfer_branches_of_card_eq
    (hc : Fintype.card I = Fintype.card J)
    (hN : IsUnit (N : Γ(U.toScheme, ⊤)))
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) (ι : J ↪ I) :
    ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι ι).ι ≫
      mixedChartFirst o o' U V).appTop
        (subframeNormalizedTransfer e o o' U hU V hV h hN v).val =
    ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι ι).ι ≫
      mixedChartSecond o o' U V).appTop v.val :=
  (subframeNormalizedTransfer_branch_iff e o o' U hU V hV h hN ι v).mpr
    (subframeTransferSelectionError_eq_zero_of_card_eq e o o' U V hV h hc ι v)

end FLT.Mazur.EquivalenceRelationNormalizedFrames

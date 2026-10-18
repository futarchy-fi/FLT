/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeImagePullback
public import FLT.Mazur.FiniteSubframeSelections

/-!
# Invariant transfer over unordered subframes

Sum the pullback of an invariant smaller-chart section once for each subset.
The resulting section is invariant under the entire larger-frame action, even
when different subsets have different pullbacks. No group order is inverted.
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
local notation "C" => SubframeSelections I (Fintype.card J)

/-- Sum each unordered subframe pullback exactly once. -/
def subframeTransferSection
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) : Γ(U.toScheme, ⊤) :=
  ∑ s : C, (subframeRefinementMap e o o' (SubframeSelections.embedding s) U V
    (h (SubframeSelections.embedding s))).appTop v.val

/-- The transfer is invariant even when individual selected pullbacks disagree. -/
theorem subframeTransferSection_invariant
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) (σ : Equiv.Perm I) :
    ((restrictedAction (action e I o) U hU σ⁻¹).hom).appTop
      (subframeTransferSection e o o' U V hV h v) =
        subframeTransferSection e o o' U V hV h v := by
  unfold subframeTransferSection
  rw [map_sum]
  calc
    _ = ∑ s : C, (subframeRefinementMap e o o'
        (SubframeSelections.embedding (SubframeSelections.permute _ σ s)) U V
          (h (SubframeSelections.embedding (SubframeSelections.permute _ σ s)))).appTop
            v.val := by
      apply Finset.sum_congr rfl
      intro s _
      change ((restrictedAction (action e I o) U hU σ⁻¹).hom ≫
        subframeRefinementMap e o o' (SubframeSelections.embedding s) U V
          (h (SubframeSelections.embedding s))).appTop v.val = _
      rw [subframeRefinement_action_source]
      exact subframePullback_eq_of_range e o o' U V hV h _ _
        (SubframeSelections.range_permute_embedding σ s).symm v
    _ = _ := (SubframeSelections.permute (Fintype.card J) σ).sum_comp
      (fun s : C ↦ (subframeRefinementMap e o o' (SubframeSelections.embedding s) U V
        (h (SubframeSelections.embedding s))).appTop v.val)

/-- The constructed invariant transfer is additive in the target section. -/
def subframeTransfer :
    invariantCoordinates (restrictedAction (action e J o') V hV) →+
      invariantCoordinates (restrictedAction (action e I o) U hU) where
  toFun v := ⟨subframeTransferSection e o o' U V hV h v, fun σ ↦ by
    rw [SchemeCoordinateAction.coordinateAction_smul]
    exact subframeTransferSection_invariant e o o' U hU V hV h v σ⟩
  map_zero' := by
    apply Subtype.ext
    simp [subframeTransferSection]
  map_add' v w := by
    apply Subtype.ext
    simp [subframeTransferSection, Finset.sum_add_distrib]

/-- Agreement of all selections recovers the binomial multiple of the common pullback. -/
theorem subframeTransferSection_of_agreement
    (v : invariantCoordinates (restrictedAction (action e J o') V hV))
    (w : Γ(U.toScheme, ⊤))
    (hw : ∀ ι : J ↪ I, (subframeRefinementMap e o o' ι U V (h ι)).appTop v.val = w) :
    subframeTransferSection e o o' U V hV h v =
      ((Fintype.card I).choose (Fintype.card J)) • w := by
  simp only [subframeTransferSection, hw, Finset.sum_const, Finset.card_univ,
    SubframeSelections.card]

end FLT.Mazur.EquivalenceRelationNormalizedFrames

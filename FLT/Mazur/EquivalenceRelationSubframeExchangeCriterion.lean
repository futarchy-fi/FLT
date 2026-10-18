/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeNormalizedCorrection
public import FLT.Mazur.FiniteEmbeddingExchangeInvariance

/-!
# Single-label exchanges detect the original subframe obstruction

Target invariance already supplies the setwise stabilizer of one selected
image. The only extra equations for source invariance exchange a selected
label with an omitted label. On the unit-degree locus these equations are
also equivalent to vanishing of the original transfer selection error.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] (o : I) (o' : J)
  (U : (source p q I o).Opens)
  (hU : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U = U)
  (V : (source p q J o').Opens)
  (hV : ∀ σ, (action e J o' σ).hom ⁻¹ᵁ V = V)
  (h : ∀ ι : J ↪ I, U ≤ subframeMap e o o' ι ⁻¹ᵁ V)
local notation "N" => Nat.choose (Fintype.card I) (Fintype.card J)

/-- Agreement under crossing exchanges is exactly invariance of a selected pullback. -/
theorem subframePullback_invariant_iff_exchanges (ι : J ↪ I)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    (∃ w : invariantCoordinates (restrictedAction (action e I o) U hU),
      w.val = (subframeRefinementMap e o o' ι U V (h ι)).appTop v.val) ↔
    ∀ a ∈ Set.range ι, ∀ b ∉ Set.range ι,
      (subframeRefinementMap e o o' (ι.trans (Equiv.swap a b).toEmbedding) U V
        (h (ι.trans (Equiv.swap a b).toEmbedding))).appTop v.val =
          (subframeRefinementMap e o o' ι U V (h ι)).appTop v.val := by
  constructor
  · intro hw a _ b _
    exact (subframePullback_invariant_iff e o o' U hU V h ι v.val).mp hw _
  · intro hs
    let _ := SchemeCoordinateAction.coordinateAction (restrictedAction (action e I o) U hU)
    let w := (subframeRefinementMap e o o' ι U V (h ι)).appTop v.val
    have hact (σ : Equiv.Perm I) : σ • w =
        (subframeRefinementMap e o o' (ι.trans σ.toEmbedding) U V
          (h (ι.trans σ.toEmbedding))).appTop v.val := by
      rw [SchemeCoordinateAction.coordinateAction_smul]
      change ((restrictedAction (action e I o) U hU σ⁻¹).hom ≫
        subframeRefinementMap e o o' ι U V (h ι)).appTop v.val = _
      rw [subframeRefinement_action_source]
      rfl
    refine ⟨⟨w, ?_⟩, rfl⟩
    apply FiniteEmbeddingExchangeInvariance.fixed_of_crossing_swaps ι w
    · intro σ hσ
      rw [hact]
      exact subframePullback_eq_of_range e o o' U V hV h _ ι hσ v
    · intro a ha b hb
      rw [hact]
      exact hs a ha b hb

include hU in
/-- On the unit-degree locus, crossing equations characterize the actual selection error. -/
theorem subframeTransferSelectionError_zero_iff_exchanges
    (hN : IsUnit (N : Γ(U.toScheme, ⊤))) (ι : J ↪ I)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    subframeTransferSelectionError e o o' U V hV h ι v = 0 ↔
    ∀ a ∈ Set.range ι, ∀ b ∉ Set.range ι,
      (subframeRefinementMap e o o' (ι.trans (Equiv.swap a b).toEmbedding) U V
        (h (ι.trans (Equiv.swap a b).toEmbedding))).appTop v.val =
          (subframeRefinementMap e o o' ι U V (h ι)).appTop v.val := by
  rw [← subframePullback_invariant_iff_exchanges e o o' U hU V hV h ι v]
  constructor
  · intro he
    exact ⟨subframeNormalizedTransfer e o o' U hU V hV h hN v,
      (subframeNormalizedTransfer_selection_iff e o o' U hU V hV h hN ι v).mpr he⟩
  · intro hw
    apply sub_eq_zero.mpr
    exact subframeTransferSection_of_agreement e o o' U V hV h v _
      ((subframePullback_invariant_iff e o o' U hU V h ι v.val).mp hw)

variable [Etale p]
open MixedFrames

/-- Single-label exchanges detect every original unscaled embedding equation. -/
theorem subframeNormalizedTransfer_branches_iff_exchanges
    (hN : IsUnit (N : Γ(U.toScheme, ⊤))) (ι : J ↪ I)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    (∀ κ : J ↪ I,
      ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι κ).ι ≫
        mixedChartFirst o o' U V).appTop
          (subframeNormalizedTransfer e o o' U hU V hV h hN v).val =
      ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι κ).ι ≫
        mixedChartSecond o o' U V).appTop v.val) ↔
    ∀ a ∈ Set.range ι, ∀ b ∉ Set.range ι,
      (subframeRefinementMap e o o' (ι.trans (Equiv.swap a b).toEmbedding) U V
        (h (ι.trans (Equiv.swap a b).toEmbedding))).appTop v.val =
          (subframeRefinementMap e o o' ι U V (h ι)).appTop v.val :=
  (subframeNormalizedTransfer_all_branches_iff e o o' U hU V hV h hN ι v).trans
    (subframeTransferSelectionError_zero_iff_exchanges e o o' U hU V hV h hN ι v)

end FLT.Mazur.EquivalenceRelationNormalizedFrames

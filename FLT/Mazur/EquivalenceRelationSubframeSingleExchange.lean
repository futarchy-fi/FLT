/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeExchangeCriterion
public import FLT.Mazur.FiniteEmbeddingSingleExchange

/-!
# One exchange detects every original strict subframe branch

Fix a selected image and one omitted label. Invariance of the target makes
internal and external relabelings automatic, so swapping the distinguished
selected label with this one omitted label tests all the missing equations.
On the unit-degree locus it detects the original selection error exactly.
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

/-- One exchange with any omitted label detects source invariance of the actual pullback. -/
theorem subframePullback_invariant_iff_one_exchange (ι : J ↪ I)
    (b₀ : I) (hb₀ : b₀ ∉ Set.range ι)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    (∃ w : invariantCoordinates (restrictedAction (action e I o) U hU),
      w.val = (subframeRefinementMap e o o' ι U V (h ι)).appTop v.val) ↔
    (subframeRefinementMap e o o' (ι.trans (Equiv.swap (ι o') b₀).toEmbedding) U V
      (h (ι.trans (Equiv.swap (ι o') b₀).toEmbedding))).appTop v.val =
        (subframeRefinementMap e o o' ι U V (h ι)).appTop v.val := by
  constructor
  · intro hw
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
    have hr (σ : Equiv.Perm I)
        (hσ : Set.range (ι.trans σ.toEmbedding : J → I) = Set.range ι) : σ • w = w := by
      rw [hact]
      exact subframePullback_eq_of_range e o o' U V hV h _ ι hσ v
    refine ⟨⟨w, ?_⟩, rfl⟩
    apply (FiniteEmbeddingExchangeInvariance.fixed_iff_one_crossing_swap
      ι w hr (ι o') b₀ ⟨o', rfl⟩ hb₀).mpr
    rw [hact]
    exact hs

include hU in
/-- A single actual exchange equation detects the unit-degree transfer selection error. -/
theorem subframeTransferSelectionError_zero_iff_one_exchange
    (hN : IsUnit (N : Γ(U.toScheme, ⊤))) (ι : J ↪ I)
    (b₀ : I) (hb₀ : b₀ ∉ Set.range ι)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    subframeTransferSelectionError e o o' U V hV h ι v = 0 ↔
    (subframeRefinementMap e o o' (ι.trans (Equiv.swap (ι o') b₀).toEmbedding) U V
      (h (ι.trans (Equiv.swap (ι o') b₀).toEmbedding))).appTop v.val =
        (subframeRefinementMap e o o' ι U V (h ι)).appTop v.val := by
  rw [subframeTransferSelectionError_zero_iff_exchanges e o o' U hU V hV h hN ι v,
    ← subframePullback_invariant_iff_exchanges e o o' U hU V hV h ι v,
    subframePullback_invariant_iff_one_exchange e o o' U hU V hV h ι b₀ hb₀ v]

include hU in
/-- Strict cardinality constructs the omitted label for an exact one-equation error test. -/
theorem exists_subframe_single_exchange_test
    (hc : Fintype.card J < Fintype.card I)
    (hN : IsUnit (N : Γ(U.toScheme, ⊤))) (ι : J ↪ I)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    ∃ b₀ ∉ Set.range ι,
      (subframeTransferSelectionError e o o' U V hV h ι v = 0 ↔
        (subframeRefinementMap e o o' (ι.trans (Equiv.swap (ι o') b₀).toEmbedding) U V
          (h (ι.trans (Equiv.swap (ι o') b₀).toEmbedding))).appTop v.val =
            (subframeRefinementMap e o o' ι U V (h ι)).appTop v.val) := by
  classical
  have hs : ¬ Function.Surjective (ι : J → I) :=
    fun hs ↦ (Nat.not_le_of_lt hc) (Fintype.card_le_of_surjective ι hs)
  obtain ⟨b₀, hb₀⟩ := not_forall.mp hs
  exact ⟨b₀, hb₀, subframeTransferSelectionError_zero_iff_one_exchange
    e o o' U hU V hV h hN ι b₀ hb₀ v⟩

variable [Etale p]
open MixedFrames

/-- Every original unscaled branch equation is detected by one chosen strict exchange. -/
theorem subframeNormalizedTransfer_branches_iff_one_exchange
    (hN : IsUnit (N : Γ(U.toScheme, ⊤))) (ι : J ↪ I)
    (b₀ : I) (hb₀ : b₀ ∉ Set.range ι)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    (∀ κ : J ↪ I,
      ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι κ).ι ≫
        mixedChartFirst o o' U V).appTop
          (subframeNormalizedTransfer e o o' U hU V hV h hN v).val =
      ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι κ).ι ≫
        mixedChartSecond o o' U V).appTop v.val) ↔
    (subframeRefinementMap e o o' (ι.trans (Equiv.swap (ι o') b₀).toEmbedding) U V
      (h (ι.trans (Equiv.swap (ι o') b₀).toEmbedding))).appTop v.val =
        (subframeRefinementMap e o o' ι U V (h ι)).appTop v.val :=
  (subframeNormalizedTransfer_all_branches_iff e o o' U hU V hV h hN ι v).trans
    (subframeTransferSelectionError_zero_iff_one_exchange
      e o o' U hU V hV h hN ι b₀ hb₀ v)

end FLT.Mazur.EquivalenceRelationNormalizedFrames

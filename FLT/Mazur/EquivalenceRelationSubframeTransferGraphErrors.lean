/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeTransferBoundary
public import FLT.Mazur.EquivalenceRelationSubframeFullDomain

/-!
# Exact graph errors remaining after unordered-subframe transfer

Invariant transfer corrects the binomial multiple of an independent source lift.
Its error on each actual embedding branch is the sum of the differences between
that selection and all unordered selections. Boundary-zero transfer corrections
alone do not establish that these remaining branch errors vanish.
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

/-- The exact error between invariant transfer and one scaled selected pullback. -/
def subframeTransferSelectionError (ι : J ↪ I)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) : Γ(U.toScheme, ⊤) :=
  subframeTransferSection e o o' U V hV h v -
    N • (subframeRefinementMap e o o' ι U V (h ι)).appTop v.val

/-- Each remaining error is a finite sum of actual selected-pullback differences. -/
theorem subframeTransferSelectionError_eq_sum (ι : J ↪ I)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    subframeTransferSelectionError e o o' U V hV h ι v =
      ∑ a : SubframeSelections I (Fintype.card J),
        ((subframeRefinementMap e o o' (SubframeSelections.embedding a) U V
          (h (SubframeSelections.embedding a))).appTop v.val -
          (subframeRefinementMap e o o' ι U V (h ι)).appTop v.val) := by
  simp only [subframeTransferSelectionError, subframeTransferSection,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, SubframeSelections.card]

/-- The correction replaces the scaled source lift by the actual invariant transfer. -/
theorem subframeTransferCorrection_correct
    (u : invariantCoordinates (restrictedAction (action e I o) U hU))
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    N • u - subframeTransferCorrection e o o' U hU V hV h u v =
      subframeTransfer e o o' U hU V hV h v := sub_sub_cancel _ _

include hU in
/-- Vanishing on one selection forces vanishing on every selection by source invariance. -/
theorem subframeTransferSelectionError_zero_all (ι : J ↪ I)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV))
    (hi : subframeTransferSelectionError e o o' U V hV h ι v = 0) (κ : J ↪ I) :
    subframeTransferSelectionError e o o' U V hV h κ v = 0 := by
  have hi' : (subframeTransfer e o o' U hU V hV h v).val =
      (subframeRefinementMap e o o' ι U V (h ι)).appTop (N • v.val) := by
    rw [map_nsmul]
    exact sub_eq_zero.mp hi
  have he := (subframePullback_invariant_iff e o o' U hU V h ι (N • v.val)).mp
    ⟨subframeTransfer e o o' U hU V hV h v, hi'⟩ κ
  apply sub_eq_zero.mpr
  calc
    _ = (subframeRefinementMap e o o' ι U V (h ι)).appTop (N • v.val) := hi'
    _ = (subframeRefinementMap e o o' κ U V (h κ)).appTop (N • v.val) := he.symm
    _ = _ := map_nsmul _ _ _

variable [Etale p]
open MixedFrames

/-- The corrected pair solves a full embedding branch exactly when its remaining error is zero. -/
theorem subframeTransferCorrection_branch_iff (ι : J ↪ I)
    (u : invariantCoordinates (restrictedAction (action e I o) U hU))
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι ι).ι ≫
      mixedChartFirst o o' U V).appTop
        (N • u - subframeTransferCorrection e o o' U hU V hV h u v).val =
    ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι ι).ι ≫
      mixedChartSecond o o' U V).appTop (N • v.val) ↔
        subframeTransferSelectionError e o o' U V hV h ι v = 0 := by
  rw [subframeTransferCorrection_correct, mixedSubframeBranch_equation_iff e o o' U V ι
    (h ι), map_nsmul]
  exact sub_eq_zero.symm

/-- One representative transfer error suffices for every actual embedding branch equation. -/
theorem subframeTransferCorrection_all_branches_iff (ι : J ↪ I)
    (u : invariantCoordinates (restrictedAction (action e I o) U hU))
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    (∀ κ : J ↪ I,
      ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι κ).ι ≫
        mixedChartFirst o o' U V).appTop
          (N • u - subframeTransferCorrection e o o' U hU V hV h u v).val =
      ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι κ).ι ≫
        mixedChartSecond o o' U V).appTop (N • v.val)) ↔
      subframeTransferSelectionError e o o' U V hV h ι v = 0 := by
  simp only [subframeTransferCorrection_branch_iff]
  exact ⟨fun hh ↦ hh ι,
    fun hi κ ↦ subframeTransferSelectionError_zero_all e o o' U hU V hV h ι v hi κ⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames

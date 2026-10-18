/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeDiscrepancy
public import FLT.Mazur.EquivalenceRelationSubframeInvariantCriterion
public import FLT.Mazur.EquivalenceRelationMixedSourceEquations

/-!
# Strict subframe corrections on the actual mixed embedding branches

The explicit discrepancy corrects the original mixed graph equation, with both
independent chart projections retained. All selections yield one invariant
corrected section precisely when their pulled-back functions agree.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (U : (source p q I o).Opens) (V : (source p q J o').Opens)

omit [Etale p] in
/-- The actual graph projections commute with the restricted subframe map. -/
@[reassoc] theorem mixedEmbeddingSource_refinement (ι : J ↪ I)
    (hUV : U ≤ subframeMap e o o' ι ⁻¹ᵁ V) :
    mixedEmbeddingSourceFirst e o o' U V ι ≫ subframeRefinementMap e o o' ι U V hUV =
      mixedEmbeddingSourceSecond e o o' U V ι := by
  apply (cancel_mono V.ι).mp
  simp only [Category.assoc, subframeRefinementMap_inclusion,
    mixedEmbeddingSourceFirst_inclusion_assoc, mixedEmbeddingSourceSecond_inclusion]

/-- The explicit raw correction solves its entire original embedding branch. -/
theorem subframeDiscrepancy_corrects_branch (ι : J ↪ I)
    (hUV : U ≤ subframeMap e o o' ι ⁻¹ᵁ V)
    (u : Γ(U.toScheme, ⊤)) (v : Γ(V.toScheme, ⊤)) :
    ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι ι).ι ≫
      mixedChartFirst o o' U V).appTop
        (u - subframeDiscrepancy e o o' ι U V hUV u v) =
      ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι ι).ι ≫
        mixedChartSecond o o' U V).appTop v := by
  apply (mixedEmbedding_equation_iff e o o' U V ι _ v).mpr
  rw [subframeDiscrepancy_correct]
  change (mixedEmbeddingSourceFirst e o o' U V ι ≫
    subframeRefinementMap e o o' ι U V hUV).appTop v = _
  rw [mixedEmbeddingSource_refinement]

/-- Agreement of all selected pullbacks constructs one invariant solution to every graph. -/
theorem exists_invariant_subframe_branch_lift
    (hU : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U = U)
    (h : ∀ ι : J ↪ I, U ≤ subframeMap e o o' ι ⁻¹ᵁ V)
    (ι : J ↪ I) (v : Γ(V.toScheme, ⊤))
    (hv : ∀ κ : J ↪ I, (subframeRefinementMap e o o' κ U V (h κ)).appTop v =
      (subframeRefinementMap e o o' ι U V (h ι)).appTop v) :
    ∃ w : invariantCoordinates (restrictedAction (action e I o) U hU),
      w.val = (subframeRefinementMap e o o' ι U V (h ι)).appTop v ∧
      ∀ κ : J ↪ I,
        ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι κ).ι ≫
          mixedChartFirst o o' U V).appTop w.val =
        ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι κ).ι ≫
          mixedChartSecond o o' U V).appTop v := by
  obtain ⟨w, hw⟩ := (subframePullback_invariant_iff e o o' U hU V h ι v).mpr hv
  refine ⟨w, hw, fun κ ↦ ?_⟩
  apply (mixedEmbedding_equation_iff e o o' U V κ w.val v).mpr
  rw [hw, ← hv κ]
  change (mixedEmbeddingSourceFirst e o o' U V κ ≫
    subframeRefinementMap e o o' κ U V (h κ)).appTop v = _
  rw [mixedEmbeddingSource_refinement]

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames

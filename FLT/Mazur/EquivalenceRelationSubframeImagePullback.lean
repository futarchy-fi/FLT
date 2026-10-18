/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeInvariantCriterion
public import Mathlib.Logic.Equiv.Set

/-!
# Invariant smaller-chart functions depend only on the selected image

The restricted target action changes the labeling of a subframe, but fixes an
invariant function. Consequently its pullback is independent of the chosen
bijection from the smaller frame to a fixed subset of the larger frame.
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
  (U : (source p q I o).Opens) (V : (source p q J o').Opens)
  (hV : ∀ σ, (action e J o' σ).hom ⁻¹ᵁ V = V)
  (h : ∀ ι : J ↪ I, U ≤ subframeMap e o o' ι ⁻¹ᵁ V)

/-- Restricted selections retain the smaller frame's actual permutation action. -/
@[reassoc] theorem subframeRefinement_action_target (ι : J ↪ I) (σ : Equiv.Perm J) :
    subframeRefinementMap e o o' ι U V (h ι) ≫
      (restrictedAction (action e J o') V hV σ).hom =
        subframeRefinementMap e o o' (σ.symm.toEmbedding.trans ι) U V
          (h (σ.symm.toEmbedding.trans ι)) := by
  apply (cancel_mono V.ι).mp
  simp only [Category.assoc, restrictedAction_hom_ι, subframeRefinementMap_inclusion_assoc,
    subframeRefinementMap_inclusion,
    subframeMap_action_target]

/-- Relabeling a selected image does not change an invariant target function's pullback. -/
theorem subframePullback_target_permute (ι : J ↪ I) (σ : Equiv.Perm J)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    (subframeRefinementMap e o o' (σ.toEmbedding.trans ι) U V
      (h (σ.toEmbedding.trans ι))).appTop v.val =
        (subframeRefinementMap e o o' ι U V (h ι)).appTop v.val := by
  have he := congrArg (fun f ↦ f.appTop v.val)
    (subframeRefinement_action_target e o o' U V hV h ι σ.symm)
  simp only [Equiv.symm_symm, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at he
  have hv := v.property σ
  rw [SchemeCoordinateAction.coordinateAction_smul] at hv
  exact he.symm.trans (congrArg (subframeRefinementMap e o o' ι U V (h ι)).appTop hv)

omit [Fintype I] [Fintype J] in
/-- Equal-image selections differ only by a permutation of their common domain. -/
theorem exists_subframe_domain_permutation (ι κ : J ↪ I)
    (hr : Set.range (ι : J → I) = Set.range (κ : J → I)) :
    ∃ σ : Equiv.Perm J, σ.toEmbedding.trans ι = κ := by
  let σ := (Equiv.ofInjective κ κ.injective).trans
    ((Set.equivOfEq hr.symm).trans (Equiv.ofInjective ι ι.injective).symm)
  refine ⟨σ, ?_⟩
  ext j
  exact Equiv.apply_ofInjective_symm ι.injective _

/-- An invariant target section pulls back identically along any two labelings of one image. -/
theorem subframePullback_eq_of_range (ι κ : J ↪ I)
    (hr : Set.range (ι : J → I) = Set.range (κ : J → I))
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    (subframeRefinementMap e o o' ι U V (h ι)).appTop v.val =
      (subframeRefinementMap e o o' κ U V (h κ)).appTop v.val := by
  obtain ⟨σ, hσ⟩ := exists_subframe_domain_permutation ι κ hr
  rw [← hσ]
  exact (subframePullback_target_permute e o o' U V hV h ι σ v).symm

end FLT.Mazur.EquivalenceRelationNormalizedFrames

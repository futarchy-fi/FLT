/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeOpenCharts
public import FLT.Mazur.FiniteGroupOpenRestriction
public import FLT.Mazur.SchemeFiniteGroupQuotient
public import Mathlib.Logic.Equiv.Fintype

/-!
# The exact invariance obstruction for a strict subframe pullback

On a stable chart where all selections land, the larger permutation action
permutes their pullbacks transitively. One pullback is invariant if and only if
all selections agree. This identifies the missing compatibility, without assuming it.
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
  (h : ∀ ι : J ↪ I, U ≤ subframeMap e o o' ι ⁻¹ᵁ V)

/-- The action on the larger chart permutes its actual restricted selection maps. -/
@[reassoc] theorem subframeRefinement_action_source (ι : J ↪ I) (σ : Equiv.Perm I) :
    (restrictedAction (action e I o) U hU σ).hom ≫
      subframeRefinementMap e o o' ι U V (h ι) =
        subframeRefinementMap e o o' (ι.trans σ.symm.toEmbedding) U V
          (h (ι.trans σ.symm.toEmbedding)) := by
  apply (cancel_mono V.ι).mp
  simp only [Category.assoc, subframeRefinementMap_inclusion, restrictedAction_hom_ι_assoc,
    subframeMap_action_source]

/-- Invariance of one selected pullback is exactly agreement of every strict selection. -/
theorem subframePullback_invariant_iff (ι : J ↪ I) (v : Γ(V.toScheme, ⊤)) :
    (∃ w : invariantCoordinates (restrictedAction (action e I o) U hU),
      w.val = (subframeRefinementMap e o o' ι U V (h ι)).appTop v) ↔
    ∀ κ : J ↪ I, (subframeRefinementMap e o o' κ U V (h κ)).appTop v =
      (subframeRefinementMap e o o' ι U V (h ι)).appTop v := by
  constructor
  · rintro ⟨w, hw⟩ κ
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair ι κ ι.injective κ.injective
    have hk : ι.trans σ.toEmbedding = κ := by
      ext j
      exact hσ j
    have he := congrArg (fun f ↦ f.appTop v)
      (subframeRefinement_action_source e o o' U hU V h ι σ.symm)
    simp only [Equiv.symm_symm, hk, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at he
    rw [← hw] at he
    have hi := w.property σ
    rw [SchemeCoordinateAction.coordinateAction_smul] at hi
    exact he.symm.trans (hi.trans hw)
  · intro hv
    refine ⟨⟨(subframeRefinementMap e o o' ι U V (h ι)).appTop v, ?_⟩, rfl⟩
    intro σ
    rw [SchemeCoordinateAction.coordinateAction_smul]
    change ((restrictedAction (action e I o) U hU σ⁻¹).hom ≫
      subframeRefinementMap e o o' ι U V (h ι)).appTop v = _
    rw [subframeRefinement_action_source]
    exact hv _

end FLT.Mazur.EquivalenceRelationNormalizedFrames

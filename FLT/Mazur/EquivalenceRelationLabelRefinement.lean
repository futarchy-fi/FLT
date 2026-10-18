/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationLabelOverlap

/-!+# Common-chart restrictions with independent distinguished labels

A stable chart contained in a transported common chart has an actual equivariant
map to that chart. Pulling back one invariant section solves every full-size
embedding equation between any two such independently labelled subcharts.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (Z : (source p q I o).Opens)
  (hZ : ∀ σ : Equiv.Perm I, (action e I o σ).hom ⁻¹ᵁ Z = Z)
  (a : I) (U : (source p q I a).Opens)
  (hU : ∀ σ : Equiv.Perm I, (action e I a σ).hom ⁻¹ᵁ U = U)
  (hUZ : U ≤ labelChange e I a o ⁻¹ᵁ Z)

/-- The actual map of a labelled subchart to its common chart. -/
def labelRefinementMap : U.toScheme ⟶ Z.toScheme :=
  (labelChange e I a o).resLE Z U hUZ

/-- The refinement retains the whole original label map. -/
@[reassoc] theorem labelRefinementMap_inclusion :
    labelRefinementMap e I o Z a U hUZ ≫ Z.ι = U.ι ≫ labelChange e I a o :=
  Scheme.Hom.resLE_comp_ι _ _

/-- Refinement commutes with every moving action. -/
@[reassoc] theorem labelRefinementMap_equivariant (σ : Equiv.Perm I) :
    (restrictedAction (action e I a) U hU σ).hom ≫
      labelRefinementMap e I o Z a U hUZ =
    labelRefinementMap e I o Z a U hUZ ≫
      (restrictedAction (action e I o) Z hZ σ).hom := by
  apply (cancel_mono Z.ι).mp
  simp only [Category.assoc, labelRefinementMap_inclusion, restrictedAction_hom_ι,
    restrictedAction_hom_ι_assoc, labelRefinementMap_inclusion_assoc]
  rw [labelChange_action]

/-- Pull back one invariant function to an independently labelled subchart. -/
def labelInvariantRestriction :
    invariantCoordinates (restrictedAction (action e I o) Z hZ) →+*
      invariantCoordinates (restrictedAction (action e I a) U hU) :=
  invariantMap _ _ (labelRefinementMap e I o Z a U hUZ)
    (labelRefinementMap_equivariant e I o Z hZ a U hU hUZ)

/-- The invariant map is precisely the actual coefficient pullback. -/
theorem labelInvariantRestriction_val
    (w : invariantCoordinates (restrictedAction (action e I o) Z hZ)) :
    (labelInvariantRestriction e I o Z hZ a U hU hUZ w).val =
      (labelRefinementMap e I o Z a U hUZ).appTop w.val := rfl

namespace MixedFrames
variable (b : I) (V : (source p q I b).Opens)
  (hV : ∀ σ : Equiv.Perm I, (action e I b σ).hom ⁻¹ᵁ V = V)
  (hVZ : V ≤ labelChange e I b o ⁻¹ᵁ Z)

/-- The two actual graph projections into the common chart differ only by its action. -/
theorem mixedLabelRefinement_action (ι : I ↪ I) :
    mixedEmbeddingSourceFirst e a b U V ι ≫ labelRefinementMap e I o Z a U hUZ ≫
      (restrictedAction (action e I o) Z hZ (Equiv.ofBijective ι
        ⟨ι.injective, Finite.surjective_of_injective ι.injective⟩).symm).hom =
    mixedEmbeddingSourceSecond e a b U V ι ≫ labelRefinementMap e I o Z b V hVZ := by
  apply (cancel_mono Z.ι).mp
  simp only [Category.assoc, labelRefinementMap_inclusion, restrictedAction_hom_ι,
    labelRefinementMap_inclusion_assoc, mixedEmbeddingSourceFirst_inclusion_assoc,
    mixedEmbeddingSourceSecond_inclusion_assoc, subframeMap_eq_label_action]
  rw [← labelChange_action]
  simp only [← labelChange_comp e I a b o, Category.assoc]

/-- One common invariant function solves all full-size equations across different labels. -/
theorem mixedLabelRefinement_source_equalizes (ι : I ↪ I)
    (w : invariantCoordinates (restrictedAction (action e I o) Z hZ)) :
    (mixedEmbeddingSourceFirst e a b U V ι).appTop
      (labelInvariantRestriction e I o Z hZ a U hU hUZ w).val =
    (mixedEmbeddingSourceSecond e a b U V ι).appTop
      (labelInvariantRestriction e I o Z hZ b V hV hVZ w).val := by
  let σ := (Equiv.ofBijective ι
    ⟨ι.injective, Finite.surjective_of_injective ι.injective⟩).symm
  have hw : (restrictedAction (action e I o) Z hZ σ).hom.appTop w.val = w.val := by
    have h := w.property σ⁻¹
    simpa only [SchemeCoordinateAction.coordinateAction_smul, inv_inv] using h
  have he := congrArg (fun f ↦ f.appTop w.val)
    (mixedLabelRefinement_action e I o Z hZ a U hUZ b V hVZ ι)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at he
  rw [hw] at he
  exact he

variable [Etale p]

/-- These constructed coefficients equalize the original mixed-chart graph branches. -/
theorem mixedLabelRefinement_branch_equalizes (ι : I ↪ I)
    (w : invariantCoordinates (restrictedAction (action e I o) Z hZ)) :
    ((mixedEmbeddingTestOpen e a b (mixedChartOpen a b U V).ι ι).ι ≫
      mixedChartFirst a b U V).appTop
        (labelInvariantRestriction e I o Z hZ a U hU hUZ w).val =
    ((mixedEmbeddingTestOpen e a b (mixedChartOpen a b U V).ι ι).ι ≫
      mixedChartSecond a b U V).appTop
        (labelInvariantRestriction e I o Z hZ b V hV hVZ w).val :=
  (mixedEmbedding_equation_iff e a b U V ι _ _).mpr
    (mixedLabelRefinement_source_equalizes e I o Z hZ a U hU hUZ b V hV hVZ ι w)

end MixedFrames
end FLT.Mazur.EquivalenceRelationNormalizedFrames

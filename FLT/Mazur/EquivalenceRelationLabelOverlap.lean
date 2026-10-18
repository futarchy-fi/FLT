/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationEqualFrameOverlap
public import FLT.Mazur.EquivalenceRelationLabelOpenCharts

/-!+# Embedding equations between independently labelled frame charts

Changing the distinguished label transports the second chart and its invariant
coefficient. Every full-size embedding equation is then an ordinary overlap
equation on the first frame scheme, including its nonreduced structure.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o o' : I)

/-- Full-size selection is label transport followed by the actual permutation action. -/
theorem subframeMap_eq_label_action (ι : I ↪ I) :
    subframeMap e o o' ι = labelChange e I o o' ≫
      (action e I o' (Equiv.ofBijective ι
        ⟨ι.injective, Finite.surjective_of_injective ι.injective⟩).symm).hom := by
  apply hom_ext_second p q I o' e
  intro j
  change subframeMap e o o' ι ≫ coordinate p q I o' j ≫ q =
    (labelChange e I o o' ≫ actionMap e I o' _) ≫ coordinate p q I o' j ≫ q
  simp only [Category.assoc, subframeMap_second, actionMap_second, labelChange_second]
  rfl

variable (V : (source p q I o').Opens)
  (hV : ∀ σ : Equiv.Perm I, (action e I o' σ).hom ⁻¹ᵁ V = V)

/-- Pull invariant coefficients back along the actual labelled chart isomorphism. -/
def labelInvariantPullback :
    invariantCoordinates (restrictedAction (action e I o') V hV) →+*
      invariantCoordinates (restrictedAction (action e I o)
        (labelChange e I o o' ⁻¹ᵁ V) (label_preimage_stable e I o o' V hV)) :=
  invariantMap _ _ (labelChartIso e I o o' V).hom
    (labelChartIso_equivariant e I o o' V hV)

/-- Label transport acts on sections by the exact scheme pullback. -/
theorem labelInvariantPullback_val
    (v : invariantCoordinates (restrictedAction (action e I o') V hV)) :
    (labelInvariantPullback e I o o' V hV v).val =
      (labelChartIso e I o o' V).hom.appTop v.val := rfl

namespace MixedFrames
variable (U : (source p q I o).Opens)
local notation "N" => source p q I o
set_option quotPrecheck false
local notation "V'" => labelChange e I o o' ⁻¹ᵁ V

include hV in
/-- Independent labels still give the entire transported ordinary overlap. -/
theorem mixedLabelDomain_eq (ι : I ↪ I) :
    mixedEmbeddingDomain e o o' U V ι = U ⊓ V' := by
  rw [mixedEmbeddingDomain_eq, subframeMap_eq_label_action,
    Scheme.Hom.comp_preimage, hV]

/-- Identify the graph source with the transported ordinary overlap. -/
def mixedLabelOverlapIso (ι : I ↪ I) :
    (U ⊓ V').toScheme ≅ (mixedEmbeddingDomain e o o' U V ι).toScheme :=
  (Scheme.isoOfEq _ (mixedLabelDomain_eq e I o o' V hV U ι)).symm

/-- The first projection is ordinary overlap restriction. -/
@[reassoc] theorem mixedLabelOverlap_first (ι : I ↪ I) :
    (mixedLabelOverlapIso e I o o' V hV U ι).hom ≫
      mixedEmbeddingSourceFirst e o o' U V ι = (N).homOfLE inf_le_left := by
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, mixedEmbeddingSourceFirst_inclusion,
    mixedLabelOverlapIso, Iso.symm_hom, Scheme.isoOfEq_inv_ι, Scheme.homOfLE_ι]

/-- The second projection retains both the label isomorphism and the permutation. -/
@[reassoc] theorem mixedLabelOverlap_second (ι : I ↪ I) :
    (mixedLabelOverlapIso e I o o' V hV U ι).hom ≫
      mixedEmbeddingSourceSecond e o o' U V ι =
    (N).homOfLE inf_le_right ≫ (labelChartIso e I o o' V).hom ≫
      (restrictedAction (action e I o') V hV (Equiv.ofBijective ι
        ⟨ι.injective, Finite.surjective_of_injective ι.injective⟩).symm).hom := by
  apply (cancel_mono V.ι).mp
  simp only [Category.assoc, mixedEmbeddingSourceSecond_inclusion,
    mixedLabelOverlapIso, Iso.symm_hom, Scheme.isoOfEq_inv_ι_assoc,
    restrictedAction_hom_ι, labelChartIso_inclusion_assoc,
    Scheme.homOfLE_ι_assoc, subframeMap_eq_label_action]

/-- Label transport reduces all full-size source equations to ordinary overlap agreement. -/
theorem mixedLabelSource_equation_iff (ι : I ↪ I) (u : Γ(U.toScheme, ⊤))
    (v : invariantCoordinates (restrictedAction (action e I o') V hV)) :
    (mixedEmbeddingSourceFirst e o o' U V ι).appTop u =
      (mixedEmbeddingSourceSecond e o o' U V ι).appTop v.val ↔
    ((N).homOfLE (U := U ⊓ V') inf_le_left).appTop u =
      ((N).homOfLE (U := U ⊓ V') inf_le_right).appTop
        (labelInvariantPullback e I o o' V hV v).val := by
  let a := (mixedLabelOverlapIso e I o o' V hV U ι).hom
  have ha : Function.Injective a.appTop := ConcreteCategory.bijective_of_isIso _ |>.injective
  let σ := (Equiv.ofBijective ι
    ⟨ι.injective, Finite.surjective_of_injective ι.injective⟩).symm
  have hv : (restrictedAction (action e I o') V hV σ).hom.appTop v.val = v.val := by
    have h := v.property σ⁻¹
    simpa only [SchemeCoordinateAction.coordinateAction_smul, inv_inv] using h
  dsimp only [σ] at hv
  rw [← ha.eq_iff]
  change (a ≫ mixedEmbeddingSourceFirst e o o' U V ι).appTop u =
    (a ≫ mixedEmbeddingSourceSecond e o o' U V ι).appTop v.val ↔ _
  rw [mixedLabelOverlap_first, mixedLabelOverlap_second]
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hv, labelInvariantPullback_val]

variable [Etale p]

/-- The criterion applies to the actual mixed chart embedding branches. -/
theorem mixedLabelBranch_equation_iff (ι : I ↪ I) (u : Γ(U.toScheme, ⊤))
    (v : invariantCoordinates (restrictedAction (action e I o') V hV)) :
    ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι ι).ι ≫
      mixedChartFirst o o' U V).appTop u =
    ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι ι).ι ≫
      mixedChartSecond o o' U V).appTop v.val ↔
    ((N).homOfLE (U := U ⊓ V') inf_le_left).appTop u =
      ((N).homOfLE (U := U ⊓ V') inf_le_right).appTop
        (labelInvariantPullback e I o o' V hV v).val :=
  (mixedEmbedding_equation_iff e o o' U V ι u v.val).trans
    (mixedLabelSource_equation_iff e I o o' V hV U ι u v)

end MixedFrames
end FLT.Mazur.EquivalenceRelationNormalizedFrames

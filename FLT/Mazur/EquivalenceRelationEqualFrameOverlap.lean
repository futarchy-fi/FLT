/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSelfEmbeddingAction

/-!
# Equal-frame graph equations are ordinary overlap equations

For two independent stable opens of the same normalized frame scheme, every
embedding graph has source their intersection. Invariance of the second
coefficient removes the permutation from its projection. This constructs the
comparison on the entire overlap, retaining its nilpotent structure.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U V : (source p q I o).Opens)
  (hV : ∀ σ : Equiv.Perm I, (action e I o σ).hom ⁻¹ᵁ V = V)
local notation "N" => source p q I o

include hV in
/-- Each embedding branch has the full ordinary overlap as its source. -/
theorem mixedEqualFrameDomain_eq (ι : I ↪ I) :
    mixedEmbeddingDomain e o o U V ι = U ⊓ V := by
  rw [mixedEmbeddingDomain_eq, subframeMap_self_eq_action, hV]

/-- The canonical identification of the actual graph domain with the ordinary overlap. -/
def mixedEqualFrameOverlapIso (ι : I ↪ I) :
    (U ⊓ V).toScheme ≅ (mixedEmbeddingDomain e o o U V ι).toScheme :=
  (Scheme.isoOfEq _ (mixedEqualFrameDomain_eq e I o U V hV ι)).symm

/-- The first graph projection becomes the unchanged overlap restriction. -/
@[reassoc] theorem mixedEqualFrameOverlap_first (ι : I ↪ I) :
    (mixedEqualFrameOverlapIso e I o U V hV ι).hom ≫
      mixedEmbeddingSourceFirst e o o U V ι = (N).homOfLE inf_le_left := by
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, mixedEmbeddingSourceFirst_inclusion,
    mixedEqualFrameOverlapIso, Iso.symm_hom, Scheme.isoOfEq_inv_ι, Scheme.homOfLE_ι]

/-- The second graph projection becomes overlap restriction followed by its actual action. -/
@[reassoc] theorem mixedEqualFrameOverlap_second (ι : I ↪ I) :
    (mixedEqualFrameOverlapIso e I o U V hV ι).hom ≫
      mixedEmbeddingSourceSecond e o o U V ι =
    (N).homOfLE inf_le_right ≫
      (restrictedAction (action e I o) V hV (Equiv.ofBijective ι
        ⟨ι.injective, Finite.surjective_of_injective ι.injective⟩).symm).hom := by
  apply (cancel_mono V.ι).mp
  simp only [Category.assoc, mixedEmbeddingSourceSecond_inclusion,
    mixedEqualFrameOverlapIso, Iso.symm_hom, Scheme.isoOfEq_inv_ι_assoc,
    restrictedAction_hom_ι, Scheme.homOfLE_ι_assoc, subframeMap_self_eq_action]

/-- Every source graph equation is exactly one ordinary coefficient overlap equation. -/
theorem mixedEqualFrameSource_equation_iff (ι : I ↪ I) (u : Γ(U.toScheme, ⊤))
    (v : invariantCoordinates (restrictedAction (action e I o) V hV)) :
    (mixedEmbeddingSourceFirst e o o U V ι).appTop u =
      (mixedEmbeddingSourceSecond e o o U V ι).appTop v.val ↔
    ((N).homOfLE (U := U ⊓ V) inf_le_left).appTop u =
      ((N).homOfLE (U := U ⊓ V) inf_le_right).appTop v.val := by
  let a := (mixedEqualFrameOverlapIso e I o U V hV ι).hom
  have ha : Function.Injective a.appTop := ConcreteCategory.bijective_of_isIso _ |>.injective
  let σ := (Equiv.ofBijective ι
    ⟨ι.injective, Finite.surjective_of_injective ι.injective⟩).symm
  have hv : (restrictedAction (action e I o) V hV σ).hom.appTop v.val = v.val := by
    have h := v.property σ⁻¹
    simpa only [SchemeCoordinateAction.coordinateAction_smul, inv_inv] using h
  dsimp only [σ] at hv
  rw [← ha.eq_iff]
  change (a ≫ mixedEmbeddingSourceFirst e o o U V ι).appTop u =
    (a ≫ mixedEmbeddingSourceSecond e o o U V ι).appTop v.val ↔ _
  rw [mixedEqualFrameOverlap_first, mixedEqualFrameOverlap_second]
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hv]

variable [Etale p]

/-- Every actual embedding-branch equation is the same ordinary overlap equation. -/
theorem mixedEqualFrameBranch_equation_iff (ι : I ↪ I) (u : Γ(U.toScheme, ⊤))
    (v : invariantCoordinates (restrictedAction (action e I o) V hV)) :
    ((mixedEmbeddingTestOpen e o o (mixedChartOpen o o U V).ι ι).ι ≫
      mixedChartFirst o o U V).appTop u =
    ((mixedEmbeddingTestOpen e o o (mixedChartOpen o o U V).ι ι).ι ≫
      mixedChartSecond o o U V).appTop v.val ↔
    ((N).homOfLE (U := U ⊓ V) inf_le_left).appTop u =
      ((N).homOfLE (U := U ⊓ V) inf_le_right).appTop v.val :=
  (mixedEmbedding_equation_iff e o o U V ι u v.val).trans
    (mixedEqualFrameSource_equation_iff e I o U V hV ι u v)

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames

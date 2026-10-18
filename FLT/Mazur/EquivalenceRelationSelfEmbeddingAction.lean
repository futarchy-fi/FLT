/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationMixedSourceEquations
public import FLT.Mazur.FiniteGroupEquivariantOpenBoundary

/-!
# Self-embedding equations from the actual permutation action

A self-embedding of a finite frame is a permutation. On any stable open,
its second source projection is the first followed by the restricted action.
This uses no completeness hypothesis on the frame or on the original relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)

/-- Finite self-selection is the inverse-label permutation action on the whole frame scheme. -/
theorem subframeMap_self_eq_action (ι : I ↪ I) :
    subframeMap e o o ι = (action e I o (Equiv.ofBijective ι
      ⟨ι.injective, Finite.surjective_of_injective ι.injective⟩).symm).hom := by
  apply hom_ext_second p q I o e
  intro i
  change subframeMap e o o ι ≫ coordinate p q I o i ≫ q =
    actionMap e I o _ ≫ coordinate p q I o i ≫ q
  rw [subframeMap_second, actionMap_second]
  rfl

namespace MixedFrames
variable [Etale p] (U : (source p q I o).Opens)
  (hU : ∀ σ : Equiv.Perm I, (action e I o σ).hom ⁻¹ᵁ U = U)

omit [Etale p] in
include hU in
/-- A finite self-embedding retains the entire stable source open as its graph domain. -/
theorem mixedSelfEmbeddingDomain_eq (ι : I ↪ I) :
    mixedEmbeddingDomain e o o U U ι = U := by
  rw [mixedEmbeddingDomain_eq, subframeMap_self_eq_action, hU, inf_idem]

omit [Etale p] in
/-- On its exact graph domain the second projection is the restricted moving action. -/
@[reassoc] theorem mixedSelfEmbeddingSource_action (ι : I ↪ I) :
    mixedEmbeddingSourceFirst e o o U U ι ≫
      (restrictedAction (action e I o) U hU (Equiv.ofBijective ι
        ⟨ι.injective, Finite.surjective_of_injective ι.injective⟩).symm).hom =
      mixedEmbeddingSourceSecond e o o U U ι := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, restrictedAction_hom_ι, ← Category.assoc,
    mixedEmbeddingSourceFirst_inclusion, mixedEmbeddingSourceSecond_inclusion,
    subframeMap_self_eq_action]

omit [Etale p] in
/-- Actual invariant coefficients solve every self-embedding equation without completeness. -/
theorem mixedSelfEmbedding_invariant_equalizes (ι : I ↪ I)
    (t : invariantCoordinates (restrictedAction (action e I o) U hU)) :
    (mixedEmbeddingSourceFirst e o o U U ι).appTop t.val =
      (mixedEmbeddingSourceSecond e o o U U ι).appTop t.val := by
  let σ := (Equiv.ofBijective ι
    ⟨ι.injective, Finite.surjective_of_injective ι.injective⟩).symm
  have ht : (restrictedAction (action e I o) U hU σ).hom.appTop t.val = t.val := by
    have h := t.property σ⁻¹
    simpa only [SchemeCoordinateAction.coordinateAction_smul, inv_inv] using h
  have h := congrArg (fun a ↦ a.appTop t.val)
    (mixedSelfEmbeddingSource_action e I o U hU ι)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  rw [ht] at h
  exact h

/-- The same equality holds on the original embedding branch with all its nilpotents. -/
theorem mixedSelfEmbedding_branch_equalizes (ι : I ↪ I)
    (t : invariantCoordinates (restrictedAction (action e I o) U hU)) :
    ((mixedEmbeddingTestOpen e o o (mixedChartOpen o o U U).ι ι).ι ≫
      mixedChartFirst o o U U).appTop t.val =
    ((mixedEmbeddingTestOpen e o o (mixedChartOpen o o U U).ι ι).ι ≫
      mixedChartSecond o o U U).appTop t.val :=
  (mixedEmbedding_equation_iff e o o U U ι t.val t.val).mpr
    (mixedSelfEmbedding_invariant_equalizes e I o U hU ι t)

end MixedFrames
end FLT.Mazur.EquivalenceRelationNormalizedFrames

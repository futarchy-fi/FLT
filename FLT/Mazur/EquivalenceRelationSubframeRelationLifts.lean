/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeFaithfulLifts
public import FLT.Mazur.SchemeRelationDoubleRestriction

/-!
# Noncomplete image descent from the full original source relation

The full relation on a source chart contains the actual arrows between frames
with the same selection. It therefore proves kernel-pair compatibility, even
outside complete opens. Action arrows also prove permutation invariance.
These constructions turn full-relation source lifts into exact image lifts;
constructing the full-relation source lift itself is still required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (U : (source p q I o).Opens)
  (hU : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U = U) (ι : J ↪ I)
local notation "k" => U.ι ≫ first p q I o
local notation "C" => compatibleFunctions
  (SchemeRelationRestriction.fst p q k) (SchemeRelationRestriction.snd p q k)
local notation "V" => subframeImageOpen e o o' U ι
local notation "hV" => subframeImageOpen_stable e o o' U hU ι
local notation "g" => subframeImageCover e o o' U ι
local notation "hSel" => subframeImage_all_domain e o o' U hU ι

omit [Etale p] in
/-- The original action arrows force full-relation source functions to be invariant. -/
theorem subframe_sourceRelation_invariant (u : C) :
    let _ := SchemeCoordinateAction.coordinateAction (restrictedAction (action e I o) U hU)
    ∀ σ : Equiv.Perm I, σ • u.val = u.val := by
  let _ := SchemeCoordinateAction.coordinateAction (restrictedAction (action e I o) U hU)
  dsimp only
  intro σ
  rw [SchemeCoordinateAction.coordinateAction_smul]
  have he := SchemeRelationRestriction.compatible_on_arrow p q k
    (U.ι ≫ actionArrow I o σ⁻¹) (𝟙 U.toScheme)
    (restrictedAction (action e I o) U hU σ⁻¹).hom
    (by rw [Category.assoc, actionArrow_first, Category.id_comp])
    (by rw [Category.assoc, actionArrow_second, ← Category.assoc,
      ← restrictedAction_hom_ι, Category.assoc]) u
  simpa only [Scheme.Hom.id_appTop, CommRingCat.id_apply] using he.symm

/-- A common subframe gives an actual full relation arrow, hence the kernel-pair equation. -/
theorem subframe_sourceRelation_kernel (u : C) :
    (pullback.fst g g).appTop u.val = (pullback.snd g g).appTop u.val := by
  let a := pullback.fst g g
  let b := pullback.snd g g
  have he : (a ≫ U.ι) ≫ subframeMap e o o' ι =
      (b ≫ U.ι) ≫ subframeMap e o o' ι := by
    rw [Category.assoc, Category.assoc, ← subframeImageCover_inclusion,
      ← Category.assoc, pullback.condition, Category.assoc]
  apply SchemeRelationRestriction.compatible_on_arrow p q k
    (subframePairArrow e o o' ι (a ≫ U.ι) (b ≫ U.ι) he) a b
  · rw [subframePairArrow_first, Category.assoc]
  · rw [subframePairArrow_second, Category.assoc]

/-- Full original source compatibility constructs the unique invariant strict image lift. -/
theorem subframe_sourceRelation_existsUnique (u : C) :
    ∃! v : invariantCoordinates (restrictedAction (action e J o') V hV),
      (g).appTop v.val = u.val :=
  subframeImageCover_kernel_existsUnique e o o' U hU ι
    ⟨u.val, subframe_sourceRelation_invariant e o U hU u⟩
    (subframe_sourceRelation_kernel e o o' U ι u)

/-- Full-relation source lifts descend with their exact boundary and all exchange equations. -/
theorem subframe_sourceRelation_boundary_lift
    {Y : Scheme} (i : Y ⟶ (subframeImageOpen e o o' U ι).toScheme)
    (u : C) (t : Γ(Y, ⊤))
    (hb : (pullback.snd i g).appTop u.val = (pullback.fst i g).appTop t) :
    ∃ v : invariantCoordinates (restrictedAction (action e J o') V hV),
      i.appTop v.val = t ∧
        ∀ κ : J ↪ I, (subframeRefinementMap e o o' κ U V (hSel κ)).appTop v.val = u.val :=
  subframeImageCover_kernel_boundary_lift e o o' U hU ι i
    ⟨u.val, subframe_sourceRelation_invariant e o U hU u⟩
    (subframe_sourceRelation_kernel e o o' U ι u) t hb

end FLT.Mazur.EquivalenceRelationNormalizedFrames

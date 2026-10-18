/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeImageCover
public import FLT.Mazur.EquivalenceRelationSubframeImagePullback
public import FLT.Mazur.EquivalenceRelationSubframeKernelPair

/-!
# Descent from complete source charts to strict subframe images

Completeness of the entire stable source chart proves kernel-pair compatibility
geometrically. Faithfully flat descent then constructs the unique smaller-chart
function; moving source invariance proves that this function is target invariant.
The complete-open hypothesis is essential here and is not asserted for arbitrary
boundary neighborhoods.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (U : (source p q I o).Opens)
  (hU : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U = U) (ι : J ↪ I)
local notation "V" => subframeImageOpen e o o' U ι
local notation "hV" => subframeImageOpen_stable e o o' U hU ι
local notation "g" => subframeImageCover e o o' U ι

/-- The image stays in every original invariant endpoint domain containing the source. -/
theorem subframeImageOpen_le_domain (E : A.Opens) (hE : p ⁻¹ᵁ E = q ⁻¹ᵁ E)
    (hUE : U ≤ first p q I o ⁻¹ᵁ E) : V ≤ first p q J o' ⁻¹ᵁ E := by
  rintro y ⟨x, hx, rfl⟩
  change x ∈ subframeMap e o o' ι ⁻¹ᵁ (first p q J o' ⁻¹ᵁ E)
  rw [subframe_preimage_domain e o o' ι E hE]
  exact hUE hx

include hU in
/-- Every selection lands in the same constructed target open. -/
theorem subframeImage_all_domain (κ : J ↪ I) : U ≤ subframeMap e o o' κ ⁻¹ᵁ V := by
  rw [subframeImageOpen_eq e o o' U hU ι κ]
  exact subframeImage_domain e o o' U κ

local notation "hSel" => subframeImage_all_domain e o o' U hU ι

/-- A section descending a source invariant is automatically invariant on the image target. -/
theorem subframeImageCover_descended_invariant
    (u : invariantCoordinates (restrictedAction (action e I o) U hU))
    (v : Γ((V).toScheme, ⊤)) (hv : (g).appTop v = u.val) :
    let _ := SchemeCoordinateAction.coordinateAction (restrictedAction (action e J o') V hV)
    ∀ σ : Equiv.Perm J, σ • v = v := by
  let _ := SchemeCoordinateAction.coordinateAction (restrictedAction (action e J o') V hV)
  have hb := (subframePullback_invariant_iff e o o' U hU V hSel ι v).mp
    ⟨u, hv.symm⟩
  dsimp only
  intro σ
  rw [SchemeCoordinateAction.coordinateAction_smul]
  apply subframeImageCover_appTop_injective e o o' U ι
  have ht := congrArg (fun f ↦ f.appTop v)
    (subframeRefinement_action_target e o o' U V hV hSel ι σ⁻¹)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at ht
  exact ht.trans (hb _)

variable (hc : (U : Set _) ⊆ completePointLocus (p := p) (q := q) I o)

include hc in
/-- Completeness constructs the full scheme kernel-pair compatibility for a source invariant. -/
theorem subframeImageCover_complete_kernelPair
    (u : invariantCoordinates (restrictedAction (action e I o) U hU)) :
    (pullback.fst g g).appTop u.val = (pullback.snd g g).appTop u.val := by
  apply completeOpen_invariant_subframe_pair e o o' ι U hU hc u
  rw [← subframeImageCover_inclusion, ← Category.assoc, pullback.condition, Category.assoc]

include hc in
/-- Every invariant on a complete stable chart descends uniquely to the strict image target. -/
theorem subframeImageCover_complete_existsUnique
    (u : invariantCoordinates (restrictedAction (action e I o) U hU)) :
    ∃! v : invariantCoordinates (restrictedAction (action e J o') V hV),
      (g).appTop v.val = u.val := by
  obtain ⟨v, hv, _⟩ := subframeImageCover_sections_existsUnique e o o' U ι u.val
    (subframeImageCover_complete_kernelPair e o o' U hU ι hc u)
  refine ⟨⟨v, subframeImageCover_descended_invariant e o o' U hU ι u v hv⟩, hv, ?_⟩
  intro w hw
  exact Subtype.ext (subframeImageCover_appTop_injective e o o' U ι (hw.trans hv.symm))

end FLT.Mazur.EquivalenceRelationNormalizedFrames

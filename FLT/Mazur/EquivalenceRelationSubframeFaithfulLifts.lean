/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeImageDescent

/-!
# Strict image lifts from full source kernel-pair equations

An invariant source section equalizing the actual selection kernel pair
descends without a completeness hypothesis. Its boundary equation is detected
on the full pulled-back boundary, and every strict selection has the same
pullback. The source kernel-pair equation remains an explicit obligation.
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
local notation "V" => subframeImageOpen e o o' U ι
local notation "hV" => subframeImageOpen_stable e o o' U hU ι
local notation "g" => subframeImageCover e o o' U ι
local notation "hSel" => subframeImage_all_domain e o o' U hU ι

/-- Full kernel-pair compatibility constructs a unique invariant image section. -/
theorem subframeImageCover_kernel_existsUnique
    (u : invariantCoordinates (restrictedAction (action e I o) U hU))
    (hu : (pullback.fst g g).appTop u.val = (pullback.snd g g).appTop u.val) :
    ∃! v : invariantCoordinates (restrictedAction (action e J o') V hV),
      (g).appTop v.val = u.val := by
  obtain ⟨v, hv, _⟩ := subframeImageCover_sections_existsUnique e o o' U ι u.val hu
  refine ⟨⟨v, subframeImageCover_descended_invariant e o o' U hU ι u v hv⟩, hv, ?_⟩
  intro w hw
  exact Subtype.ext (subframeImageCover_appTop_injective e o o' U ι (hw.trans hv.symm))

/-- Descent of one source invariant identifies every selection pullback, including exchanges. -/
theorem subframeImageCover_descended_all
    (u : invariantCoordinates (restrictedAction (action e I o) U hU))
    (v : invariantCoordinates (restrictedAction (action e J o') V hV))
    (hv : (g).appTop v.val = u.val) (κ : J ↪ I) :
    (subframeRefinementMap e o o' κ U V (hSel κ)).appTop v.val = u.val := by
  have he := (subframePullback_invariant_iff e o o' U hU V hSel ι v.val).mp
    ⟨u, hv.symm⟩ κ
  exact he.trans hv

/-- The full pulled-back boundary detects the exact boundary of the descended section. -/
theorem subframeImageCover_descended_boundary
    {Y : Scheme} (i : Y ⟶ (subframeImageOpen e o o' U ι).toScheme)
    (u : Γ(U.toScheme, ⊤)) (v : Γ((V).toScheme, ⊤)) (hv : (g).appTop v = u)
    (t : Γ(Y, ⊤))
    (hb : (pullback.snd i g).appTop u = (pullback.fst i g).appTop t) :
    i.appTop v = t := by
  apply appTop_injective (pullback.fst i g)
  change (pullback.fst i g ≫ i).appTop v = (pullback.fst i g).appTop t
  rw [pullback.condition]
  change (pullback.snd i g).appTop ((g).appTop v) = _
  rw [hv, hb]

/-- Source equations construct an image lift with exact boundary and every selection equation. -/
theorem subframeImageCover_kernel_boundary_lift
    {Y : Scheme} (i : Y ⟶ (subframeImageOpen e o o' U ι).toScheme)
    (u : invariantCoordinates (restrictedAction (action e I o) U hU))
    (hu : (pullback.fst g g).appTop u.val = (pullback.snd g g).appTop u.val)
    (t : Γ(Y, ⊤))
    (hb : (pullback.snd i g).appTop u.val = (pullback.fst i g).appTop t) :
    ∃ v : invariantCoordinates (restrictedAction (action e J o') V hV),
      i.appTop v.val = t ∧
        ∀ κ : J ↪ I, (subframeRefinementMap e o o' κ U V (hSel κ)).appTop v.val = u.val := by
  obtain ⟨v, hv, _⟩ := subframeImageCover_kernel_existsUnique e o o' U hU ι u hu
  exact ⟨v, subframeImageCover_descended_boundary e o o' U ι i u.val v.val hv t hb,
    subframeImageCover_descended_all e o o' U hU ι u v hv⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames

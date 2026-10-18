/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeRelationLifts

/-!
# Full mixed compatibility of noncomplete image lifts

Faithful pullback of the second mixed endpoint to the strict-image cover
reduces the entire mixed equation to the full source relation. The transition
arrow is composed with the inverse selected coordinate. This includes the
residual mixed open and does not require complete frames.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
open SchemeEffectiveEpiSections EquivalenceRelationFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (U : (source p q I o).Opens) (ι : J ↪ I)
local notation "V" => subframeImageOpen e o o' U ι
local notation "g" => subframeImageCover e o o' U ι
local notation "k" => U.ι ≫ first p q I o
local notation "C" => compatibleFunctions
  (SchemeRelationRestriction.fst p q k) (SchemeRelationRestriction.snd p q k)
local notation "F" => mixedChartFirst o o' U V
local notation "H" => mixedChartSecond o o' U V
local notation "M" => mixedChartOpen o o' U V

/-- A full source relation function descending to the image solves the entire mixed equation. -/
theorem sourceRelation_subframeImage_mixed (u : C) (v : Γ((V).toScheme, ⊤))
    (hv : (g).appTop v = u.val) : (F).appTop u.val = (H).appTop v := by
  let c := pullback.fst H g
  let b := pullback.snd H g
  let a := c ≫ F
  let d := c ≫ (M).ι ≫ arrow p q I J o o'
  let z := b ≫ U.ι ≫ coordinate p q I o (ι o')
  have hd : d ≫ p = a ≫ k := by
    simp only [d, a, Category.assoc, arrow_first, mixedChartFirst,
      Scheme.Hom.resLE_comp_ι_assoc]
  have hz : z ≫ p = b ≫ k := by
    simp only [z, Category.assoc, coordinate_first]
  have he : d ≫ q = z ≫ q := by
    change c ≫ (M).ι ≫ arrow p q I J o o' ≫ q =
      b ≫ U.ι ≫ coordinate p q I o (ι o') ≫ q
    rw [arrow_second]
    have hcover := congrArg (fun f ↦ f ≫ (V).ι ≫ first p q J o')
      (pullback.condition (f := H) («g» := g))
    simpa only [c, b, Category.assoc, mixedChartSecond, Scheme.Hom.resLE_comp_ι_assoc,
      subframeImageCover_inclusion_assoc, subframeMap_first] using hcover
  let w := compose e d (z ≫ e.s) (by
    change d ≫ q = z ≫ e.s ≫ p
    rw [e.symmetry₁]
    exact he)
  have hw₁ : w ≫ p = a ≫ k := by rw [compose_fst]; exact hd
  have hw₂ : w ≫ q = b ≫ k := by
    rw [compose_snd, Category.assoc, e.symmetry₂]
    exact hz
  apply appTop_injective c
  change (c ≫ F).appTop u.val = (c ≫ H).appTop v
  rw [pullback.condition]
  change a.appTop u.val = b.appTop ((g).appTop v)
  rw [hv]
  exact SchemeRelationRestriction.compatible_on_arrow p q k w a b hw₁ hw₂ u

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames

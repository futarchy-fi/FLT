/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertTranslationSourceCartesian
public import FLT.Mazur.AffineHilbertInvariantEnvelope

/-!
# Pulling original invariant coefficients to the actual refined source

The coefficient map is geometric pullback on functions. Its principal loci
are the actual inverse images, and original admissibility survives the full
Cartesian envelope comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "u" => translationSourceMap f d b k
local notation "l" => translationSourceChart f d b k
local notation "c'" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c

local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "p'" => fst f hL d W c' l
local notation "q'" => snd f hL d W c' l
local notation "C" => compatibleFunctions (Over.Hom.left p) (Over.Hom.left q)
local notation "C'" => compatibleFunctions (Over.Hom.left p') (Over.Hom.left q')

/-- Original invariant functions pull back to invariants for the FULL refined relation. -/
theorem translationSourceCoefficient_mem (r : C) :
    (u).left.appTop r.val ∈ C' := by
  change ((p').left ≫ (u).left).appTop r.val =
    ((q').left ≫ (u).left).appTop r.val
  rw [← Over.comp_left, ← Over.comp_left, ← translationSourceRelationMap_fst,
    ← translationSourceRelationMap_snd]
  change (translationSourceRelationMap f hL d b c k).left.appTop
      ((p).left.appTop r.val) =
    (translationSourceRelationMap f hL d b c k).left.appTop ((q).left.appTop r.val)
  exact congrArg _ r.property

/-- The ring map transports original coefficients to the constructed source by actual pullback. -/
def translationSourceCoefficients : C →+* C' :=
  ((u).left.appTop.hom.comp (C).subtype).codRestrict _
    (translationSourceCoefficient_mem f hL d b c k)

/-- The pulled coefficient has precisely its geometric pullback value. -/
theorem translationSourceCoefficients_val (r : C) :
    (translationSourceCoefficients f hL d b c k r).val = (u).left.appTop r.val := rfl

/-- Nonvanishing is transported along the actual source map, not an unchanged-source comparison. -/
theorem translationSourceCoefficients_basicOpen (r : C) :
    (translationSource f d b k).left.basicOpen
        (translationSourceCoefficients f hL d b c k r).val =
      (u).left ⁻¹ᵁ A.left.basicOpen r.val :=
  (Scheme.Hom.preimage_basicOpen_top (u).left r.val).symm

variable [IsOpenImmersion k.left]

/-- Every original admissible coefficient is admissible on the actual refined translation source. -/
theorem translationSourceCoefficients_admissible (r : C)
    (hr : r ∈ invariantEnvelopeDenominators f hL d V c k) :
    translationSourceCoefficients f hL d b c k r ∈
      invariantEnvelopeDenominators f hL d W c' l := by
  rw [mem_invariantEnvelopeDenominators] at hr ⊢
  let g := (prod.map u b).left
  have hp : g ≫ (prod.fst : prod A V ⟶ A).left =
      (prod.fst : prod (translationSource f d b k) W ⟶ _).left ≫ (u).left :=
    congrArg Over.Hom.left (prod.map_fst u b)
  intro y hy
  have H : g y ∈ (prod.fst : prod A V ⟶ A).left ⁻¹ᵁ A.left.basicOpen r.val := by
    change (g ≫ (prod.fst : prod A V ⟶ A).left) y ∈ A.left.basicOpen r.val
    rw [hp]
    change (prod.fst : prod (translationSource f d b k) W ⟶ _).left y ∈
      (u).left ⁻¹ᵁ A.left.basicOpen r.val
    rw [← translationSourceCoefficients_basicOpen f hL d b c k r]
    exact hy
  obtain ⟨z, hz⟩ := hr H
  obtain ⟨a, _, ha⟩ := Scheme.exists_preimage_of_isPullback
    (translationSourceEnvelope_schemeIsPullback f hL d b c k) z y hz
  exact ⟨a, ha⟩

/-- Existing original nonvanishing coefficients remain nonvanishing on the new source. -/
theorem translationSource_nonvanishing_of_original (x : (translationSource f d b k).left)
    (h : ∃ r : C, r ∈ invariantEnvelopeDenominators f hL d V c k ∧
      (u).left x ∈ A.left.basicOpen r.val) :
    ∃ r : C', r ∈ invariantEnvelopeDenominators f hL d W c' l ∧
      x ∈ (translationSource f d b k).left.basicOpen r.val := by
  obtain ⟨r, hr, hx⟩ := h
  refine ⟨translationSourceCoefficients f hL d b c k r,
    translationSourceCoefficients_admissible f hL d b c k r hr, ?_⟩
  rw [translationSourceCoefficients_basicOpen]
  exact hx

end FLT.Mazur.HilbertChart.AffineRestriction

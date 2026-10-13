/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertTranslationEnvelope
public import FLT.Mazur.AffineHilbertTranslationSource
public import FLT.Mazur.AffineHilbertInvariantEnvelope

/-!
# Actual admissible coefficients under translation refinement

Original invariant coefficients retain their values, nonvanishing loci and
admissibility when the independent translation envelope is restricted.
The refined relation remains the full original relation on the source.
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
  {B : Over (Spec (.of R))} (l : B ⟶ variableHilbertTest f d W)
local notation "c'" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c
local notation "k" => l ≫ baseMarkedChartChange f b d

/-- Retain the very same source function in the refined ORIGINAL invariant ring. -/
def translationInvariantCoefficient
    (r : compatibleFunctions (fst f hL d V c k).left (snd f hL d V c k).left) :
    compatibleFunctions (fst f hL d W c' l).left (snd f hL d W c' l).left :=
  ⟨r.val, (relationIso_invariant_iff _ _ _ _
    ((Over.forget _).mapIso (translationRelationIso f hL d b c l))
    (congrArg Over.Hom.left (translationRelationMap_fst f hL d b c l))
    (congrArg Over.Hom.left (translationRelationMap_snd f hL d b c l)) r.val).mp r.property⟩

/-- Nonvanishing is unchanged because no source coefficient was replaced. -/
theorem translationInvariantCoefficient_basicOpen
    (r : compatibleFunctions (fst f hL d V c k).left (snd f hL d V c k).left) :
    B.left.basicOpen (translationInvariantCoefficient f hL d b c l r).val =
      B.left.basicOpen r.val := rfl

variable [IsOpenImmersion b.left] [IsOpenImmersion l.left]
local instance : Mono b := Over.mono_of_mono_left b
local instance : IsOpenImmersion (l ≫ baseMarkedChartChange f b d).left := by
  change IsOpenImmersion (l.left ≫ (baseMarkedChartChange f b d).left)
  infer_instance

/-- A coefficient filling the old envelope also fills the actual smaller translation envelope. -/
theorem translationInvariantCoefficient_admissible
    (r : compatibleFunctions (fst f hL d V c k).left (snd f hL d V c k).left)
    (hr : r ∈ invariantEnvelopeDenominators f hL d V c k) :
    translationInvariantCoefficient f hL d b c l r ∈
      invariantEnvelopeDenominators f hL d W c' l := by
  rw [mem_invariantEnvelopeDenominators] at hr ⊢
  let g := (prod.map (𝟙 B) b).left
  have hp : g ≫ (prod.fst : prod B V ⟶ B).left =
      (prod.fst : prod B W ⟶ B).left := by
    simpa only [Over.comp_left, Over.id_left, Category.comp_id] using
      congrArg Over.Hom.left (prod.map_fst (𝟙 B) b)
  intro y hy
  have h : g y ∈ (prod.fst : prod B V ⟶ B).left ⁻¹ᵁ B.left.basicOpen r.val := by
    change (g ≫ (prod.fst : prod B V ⟶ B).left) y ∈ B.left.basicOpen r.val
    rw [hp]
    exact hy
  obtain ⟨z, hz⟩ := hr h
  obtain ⟨a, _, ha⟩ := Scheme.exists_preimage_of_isPullback
    (translationEnvelope_isPullback f hL d b c l) z y hz
  exact ⟨a, ha⟩

/-- Existing nonvanishing admissible coefficients survive a genuine translation refinement. -/
theorem translation_nonvanishing_of_original (x : B.left)
    (h : ∃ r : compatibleFunctions (fst f hL d V c k).left (snd f hL d V c k).left,
      r ∈ invariantEnvelopeDenominators f hL d V c k ∧ x ∈ B.left.basicOpen r.val) :
    ∃ r : compatibleFunctions (fst f hL d W c' l).left (snd f hL d W c' l).left,
      r ∈ invariantEnvelopeDenominators f hL d W c' l ∧ x ∈ B.left.basicOpen r.val := by
  obtain ⟨r, hr, hx⟩ := h
  exact ⟨translationInvariantCoefficient f hL d b c l r,
    translationInvariantCoefficient_admissible f hL d b c l r hr, hx⟩

end FLT.Mazur.HilbertChart.AffineRestriction

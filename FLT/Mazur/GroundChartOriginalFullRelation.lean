/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseRelationSchemeLift

/-!
# The full original relation on a changed-ground source

Recompute the original Picard relation on the changed source after forgetting
its new ground. Its endpoints may have independent new-ground maps. The
changed-family relation embeds into this full relation; an original arrow
lifts precisely when its two entire new-ground morphisms agree.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open FCurve CartierAbel SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd
variable {R S : Type} [CommRing R] [CommRing S]
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of S) ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) (W : Over (Spec (.of S)))
  (t : (Over.map a).obj W ⟶ V) (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "q" => pullback.snd f a
local instance groundOriginalRelationSmooth : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "h" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
variable {B : Over (Spec (.of S))} (l : B ⟶ variableHilbertTest (pullback.snd f a) d W)

/-- View the new source as an original parameter, with no equality of new-ground maps imposed. -/
def groundOriginalChart : (Over.map a).obj B ⟶ variableHilbertTest f d V :=
  (Over.map a).map l ≫ variableHilbertFixedBaseProjection f a hL d V W t

local notation "k" => groundOriginalChart f a hL d V W t l
local notation "D" => relation f hL d V c k
local notation "D'" => relation q h d W c' l
local notation "p" => fst f hL d V c k
local notation "s" => snd f hL d V c k
local notation "p'" => fst q h d W c' l
local notation "s'" => snd q h d W c' l

/-- The new-family relation maps into the full original relation on the same source. -/
def groundRelationInclusion : (Over.map a).obj D' ⟶ D :=
  fixedBaseRelationMap f a hL d V W t c k l (𝟙 _) (Category.id_comp _)

local notation "r" => groundRelationInclusion f a hL d V W t c l

@[reassoc]
theorem groundRelationInclusion_fst : r ≫ p = (Over.map a).map p' := by
  rw [groundRelationInclusion, fixedBaseRelationMap_fst, Category.comp_id]

@[reassoc]
theorem groundRelationInclusion_snd : r ≫ s = (Over.map a).map s' := by
  rw [groundRelationInclusion, fixedBaseRelationMap_snd, Category.comp_id]

/-- Every full original arrow lifts uniquely once the two new-ground maps agree. -/
theorem groundRelationInclusion_lift {Z : Scheme} (z : Z ⟶ (D).left)
    (hb : z ≫ (p).left ≫ B.hom = z ≫ (s).left ≫ B.hom) :
    ∃! v : Z ⟶ (D').left,
      v ≫ (p').left = z ≫ (p).left ∧
      v ≫ (s').left = z ≫ (s).left ∧ v ≫ (r).left = z := by
  exact fixedBaseRelationMap_scheme_lift f a hL d V W t c k l (𝟙 _)
    (Category.id_comp _) (z ≫ (p).left) (z ≫ (s).left)
    (by simpa only [Category.assoc] using hb) z
    (Category.comp_id _).symm
    (Category.comp_id _).symm

/-- Existence of a lift detects equality of whole ground morphisms, including nilpotents. -/
theorem groundRelationInclusion_lift_iff {Z : Scheme} (z : Z ⟶ (D).left) :
    (∃ v : Z ⟶ (D').left, v ≫ (r).left = z) ↔
      z ≫ (p).left ≫ B.hom = z ≫ (s).left ≫ B.hom := by
  constructor
  · rintro ⟨v, rfl⟩
    have hp := congrArg Over.Hom.left (groundRelationInclusion_fst f a hL d V W t c l)
    have hs := congrArg Over.Hom.left (groundRelationInclusion_snd f a hL d V W t c l)
    simp only [Over.comp_left, Over.map_map_left] at hp hs
    simp only [Category.assoc]
    rw [← Category.assoc (r).left (p).left, hp,
      ← Category.assoc (r).left (s).left, hs, (p').w, (s').w]
  · intro hb
    obtain ⟨v, hv, _⟩ := groundRelationInclusion_lift f a hL d V W t c l z hb
    exact ⟨v, hv.2.2⟩

end FLT.Mazur.HilbertChart.AffineRestriction

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertRelationOperations
public import FLT.Mazur.BaseMarkedHilbertChartChange

/-!
# Full original relations under genuine translation refinements

Changing the translation and pulling back its Picard class keeps the full
relation on any source mapping to the refined chart. No coefficient-base
localization or effectiveness assumption is involved.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
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

/-- The source retains precisely its original Picard section after translation refinement. -/
theorem translation_sectionAt : sectionAt f hL d V c k = sectionAt f hL d W c' l := by
  simpa only [sectionAt, variableChartSection_map, baseMarkedIndexChange] using
    baseMarkedChartChange_class f hL b (d, c) l

/-- The actual original full relation arrow of a refined equal-class pair. -/
def translationRelationMap : relation f hL d W c' l ⟶ relation f hL d V c k :=
  arrow f hL d V c k (fst f hL d W c' l) (snd f hL d W c' l) (by
    rw [translation_sectionAt]
    exact equal_class f hL d W c' l)

@[reassoc]
theorem translationRelationMap_fst : translationRelationMap f hL d b c l ≫
    fst f hL d V c k = fst f hL d W c' l := arrow_fst f hL d V c k _ _ _

@[reassoc]
theorem translationRelationMap_snd : translationRelationMap f hL d b c l ≫
    snd f hL d V c k = snd f hL d W c' l := arrow_snd f hL d V c k _ _ _

/-- Every original relation arrow on this source survives the translation refinement. -/
def translationRelationInverse : relation f hL d V c k ⟶ relation f hL d W c' l :=
  arrow f hL d W c' l (fst f hL d V c k) (snd f hL d V c k) (by
    rw [← translation_sectionAt f hL d b c l]
    exact equal_class f hL d V c k)

@[reassoc]
theorem translationRelationInverse_fst : translationRelationInverse f hL d b c l ≫
    fst f hL d W c' l = fst f hL d V c k := arrow_fst f hL d W c' l _ _ _

@[reassoc]
theorem translationRelationInverse_snd : translationRelationInverse f hL d b c l ≫
    snd f hL d W c' l = snd f hL d V c k := arrow_snd f hL d W c' l _ _ _

/-- This is the FULL original relation, including both independently varying endpoints. -/
def translationRelationIso : relation f hL d W c' l ≅ relation f hL d V c k where
  hom := translationRelationMap f hL d b c l
  inv := translationRelationInverse f hL d b c l
  hom_inv_id := by
    apply hom_ext f hL d W c' l
    · rw [Category.assoc, translationRelationInverse_fst,
        translationRelationMap_fst, Category.id_comp]
    · rw [Category.assoc, translationRelationInverse_snd,
        translationRelationMap_snd, Category.id_comp]
  inv_hom_id := by
    apply hom_ext f hL d V c k
    · rw [Category.assoc, translationRelationMap_fst,
        translationRelationInverse_fst, Category.id_comp]
    · rw [Category.assoc, translationRelationMap_snd,
        translationRelationInverse_snd, Category.id_comp]

end FLT.Mazur.HilbertChart.AffineRestriction

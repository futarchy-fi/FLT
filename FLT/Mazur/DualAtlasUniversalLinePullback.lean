/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasUniversalLine
public import FLT.Mazur.DualAtlasGeometricComposition
public import FLT.Mazur.DualAtlasLinePullbackCoherence

/-!
# Pullback of the original universal retained line

The actual universal source and inclusion pull back along every original atlas
morphism. Their section recovers that morphism over the unchanged test base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.DualAtlasUniversalLine
open FCurve DualAtlasLineQuotient LocallyFreeDualProjectiveAtlas
variable {S T : Scheme.{u}} (M : S.Modules) (hM : LocallyFiniteFree M) (g : T ⟶ S)
variable (a : T ⟶ space M hM) (ha : a ≫ projection M hM = g)

/-- Pull the actual universal retained line and normalize its original ambient sheaf. -/
@[irreducible] def pulledLine : Line ((pullback g).obj M) :=
  ((universalLine M hM).baseChange a).changeAmbient
    ((SheafPullbackPathComparison.comparison a (projection M hM) g ha).app M)

/-- The pulled original inclusion has the independently given original atlas morphism. -/
lemma pulledLine_map :
    (toSection _ (hM.pullback g) (pulledLine M hM g a ha)).val ≫
      DualAtlasBaseChangeCharts.map g M hM = a := by
  unfold pulledLine
  rw [← sectionChangeAmbient_toSection _ _ (hM.pullback g),
    DualAtlasAmbient.sectionChangeAmbient_val, Category.assoc,
    ← DualAtlasBaseChangeCharts.map_path a (projection M hM) M hM g ha,
    ← Category.assoc]
  change (LocallySplitLineAtlasSection.morphism _ _ _ _ ≫
    DualAtlasBaseChangeCharts.map a _ _) ≫ _ = _
  dsimp only [Line.baseChange]
  rw [DualAtlasBaseChangeCharts.reverse_square, Category.assoc]
  change a ≫ ((toSection _ _ (universalLine M hM)).val ≫ _) = a
  rw [universalLine_map, Category.comp_id]

/-- Pulling the actual universal line recovers the cartesian section of the original morphism. -/
lemma pulledLine_section :
    toSection _ (hM.pullback g) (pulledLine M hM g a ha) =
      sectionOfMorphism M hM g a ha := by
  apply Subtype.ext
  apply (DualAtlasBaseChangeCharts.map_isPullback g M hM).hom_ext
  · rw [pulledLine_map, sectionOfMorphism_map]
  · exact (toSection _ _ _).property.trans (sectionOfMorphism M hM g a ha).property.symm

end FLT.Mazur.DualAtlasUniversalLine

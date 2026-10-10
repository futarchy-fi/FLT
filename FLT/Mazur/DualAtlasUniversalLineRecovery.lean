/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasUniversalLinePullback

/-!
# Recovery of the original retained source from the universal line

The independently pulled universal inclusion has the original atlas morphism,
so line classification gives an actual isomorphism to the retained source.
The source equation includes the genuine ambient path comparison.
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
variable (b : Line ((pullback g).obj M))

/-- The atlas morphism of the original retained inclusion over the test base. -/
def lineMorphism : T ⟶ space M hM :=
  (toSection _ (hM.pullback g) b).val ≫ DualAtlasBaseChangeCharts.map g M hM

/-- The original line morphism lies over its unchanged test-base map. -/
lemma lineMorphism_projection : lineMorphism M hM g b ≫ projection M hM = g := by
  rw [lineMorphism, Category.assoc, DualAtlasBaseChangeCharts.map_projection,
    ← Category.assoc, (toSection _ (hM.pullback g) b).property, Category.id_comp]

/-- Pulling the universal line along the original line morphism recovers its original section. -/
lemma pulledLine_lineMorphism_section :
    toSection _ (hM.pullback g)
        (pulledLine M hM g (lineMorphism M hM g b) (lineMorphism_projection M hM g b)) =
      toSection _ (hM.pullback g) b := by
  apply Subtype.ext
  apply (DualAtlasBaseChangeCharts.map_isPullback g M hM).hom_ext
  · exact pulledLine_map M hM g _ _
  · exact (toSection _ _ _).property.trans (toSection _ _ b).property.symm

/-- The actual pulled universal retained source is isomorphic to the original source. -/
lemma recovery_exists :
    ∃ e : (pulledLine M hM g (lineMorphism M hM g b)
        (lineMorphism_projection M hM g b)).source ≅ b.source,
      e.hom ≫ b.inclusion =
        (pulledLine M hM g (lineMorphism M hM g b)
          (lineMorphism_projection M hM g b)).inclusion :=
  (toSection_eq_iff _ (hM.pullback g) _ b).mp (pulledLine_lineMorphism_section M hM g b)

/-- The retained-source recovery isomorphism, chosen from the proved classification. -/
@[irreducible] def recoveryIso :
    (pullback (lineMorphism M hM g b)).obj (universalLine M hM).source ≅ b.source := by
  have h := recovery_exists M hM g b
  unfold pulledLine at h
  exact h.choose

/-- Source recovery preserves the original inclusion with its genuine ambient normalization. -/
lemma recoveryIso_inclusion :
    (recoveryIso M hM g b).hom ≫ b.inclusion =
      (pullback (lineMorphism M hM g b)).map (universalLine M hM).inclusion ≫
        (SheafPullbackPathComparison.comparison (lineMorphism M hM g b)
          (projection M hM) g (lineMorphism_projection M hM g b)).hom.app M := by
  unfold recoveryIso
  have h := (recovery_exists M hM g b).choose_spec
  unfold pulledLine at h
  exact h

end FLT.Mazur.DualAtlasUniversalLine

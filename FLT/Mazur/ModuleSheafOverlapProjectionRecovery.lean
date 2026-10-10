/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOverlapImageTransition

/-!
# Recovery through a common chart coordinate

An ambient projection whose pullback recovers a chart module retains that
recovery after an arbitrary further pullback and normalization of the path.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleSheafOverlapImageTransition
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {W X Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]
variable {G : X.Modules} {M : Y.Modules} (q : G ⟶ (pushforward i).obj M)
variable (e : (pullback i).obj G ≅ M)
variable (he : e.hom = (pullback i).map q ≫ (openCounitIso i M).hom)

include he in
/-- Pulling recovery through a coordinate equals pulling its ambient projection. -/
@[reassoc]
lemma coordinateIso_projection (a : W ⟶ Y) (r : W ⟶ X) (h : a ≫ i = r) :
    (comparison a i r h).inv.app G ≫ (pullback a).map e.hom =
      (pullback r).map q ≫ (coordinateIso a i r h M).hom := by
  rw [he, Functor.map_comp]
  have hn := (comparison a i r h).inv.naturality q
  dsimp only [Functor.comp_map] at hn
  simp only [coordinateIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  rw [← Category.assoc, ← hn, Category.assoc]

end FLT.Mazur.ModuleSheafOverlapImageTransition

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOverlapImageTransition

/-!
# Naturality of open-chart coordinates

The counit and path comparisons identify restrictions of ambient pushforwards
with chart pullbacks naturally in the original module.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleSheafOverlapImageTransition
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {O X Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]
variable {M N : Y.Modules}

/-- Recovery by the open counit commutes with every original module map. -/
@[reassoc]
lemma openCounitIso_naturality (f : M ⟶ N) :
    (pullback i).map ((pushforward i).map f) ≫ (openCounitIso i N).hom =
      (openCounitIso i M).hom ≫ f := by
  simp only [openCounitIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom]
  rw [(restrictFunctorIsoPullback i).inv.naturality_assoc]
  have hc := (restrictFunctorAdjCounitIso i).hom.naturality f
  dsimp only [Functor.comp_map, Functor.id_map] at hc
  rw [hc, Category.assoc]

/-- Coordinate recovery is natural in the chart module. -/
@[reassoc]
lemma coordinateIso_naturality (p : O ⟶ Y) (r : O ⟶ X) (h : p ≫ i = r)
    (f : M ⟶ N) :
    (pullback r).map ((pushforward i).map f) ≫ (coordinateIso p i r h N).hom =
      (coordinateIso p i r h M).hom ≫ (pullback p).map f := by
  simp only [coordinateIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  rw [(comparison p i r h).inv.naturality_assoc]
  change (comparison p i r h).inv.app ((pushforward i).obj M) ≫
    (pullback p).map ((pullback i).map ((pushforward i).map f)) ≫
      (pullback p).map (openCounitIso i N).hom = _
  rw [← Functor.map_comp, openCounitIso_naturality, Functor.map_comp, Category.assoc]

/-- Inverse coordinates satisfy the same naturality square. -/
@[reassoc]
lemma coordinateIso_inv_naturality (p : O ⟶ Y) (r : O ⟶ X) (h : p ≫ i = r)
    (f : M ⟶ N) :
    (pullback p).map f ≫ (coordinateIso p i r h N).inv =
      (coordinateIso p i r h M).inv ≫ (pullback r).map ((pushforward i).map f) := by
  apply (cancel_epi (coordinateIso p i r h M).hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← coordinateIso_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.ModuleSheafOverlapImageTransition

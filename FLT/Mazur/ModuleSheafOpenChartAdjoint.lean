/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOpenImmersionSections

/-!
# Adjoint chart maps and their coordinate recovery

A morphism into an original chart module gives an ambient pushforward map.
Pulling this map to any chart coordinate recovers the original morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleSheafOpenChartAdjoint
open ModuleSheafOverlapImageTransition ModuleSheafOpenImmersionSections
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {W X Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]
variable {S : X.Modules} {M : Y.Modules}

/-- The adjoint into the original chart pushforward. -/
@[irreducible] def chartAdjoint (q : (pullback i).obj S ⟶ M) :
    S ⟶ (pushforward i).obj M :=
  (pullbackPushforwardAdjunction i).homEquiv S M q

/-- Pullback and the open counit recover the entire original chart map. -/
@[reassoc] theorem chartAdjoint_recovery (q : (pullback i).obj S ⟶ M) :
    (pullback i).map (chartAdjoint i q) ≫ (openCounitIso i M).hom = q := by
  rw [openCounitIso_hom]
  unfold chartAdjoint
  exact ((pullbackPushforwardAdjunction i).homEquiv S M).symm_apply_apply q

/-- Recovery remains valid on every coordinate of the original chart. -/
@[reassoc] theorem chartAdjoint_coordinate (q : (pullback i).obj S ⟶ M)
    (p : W ⟶ Y) (r : W ⟶ X) (h : p ≫ i = r) :
    (pullback r).map (chartAdjoint i q) ≫ (coordinateIso p i r h M).hom =
      (comparison p i r h).inv.app S ≫ (pullback p).map q := by
  conv_rhs => rw [← chartAdjoint_recovery i q, Functor.map_comp]
  have hn := (comparison p i r h).inv.naturality (chartAdjoint i q)
  dsimp only [Functor.comp_map] at hn
  simp only [coordinateIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  rw [← Category.assoc, hn, Category.assoc]

end FLT.Mazur.ModuleSheafOpenChartAdjoint

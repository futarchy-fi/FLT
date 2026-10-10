/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentPairNormalization
public import FLT.Mazur.SchemeOverlapDiagonalChart

/-!
# Detecting the original diagonal law by normalized identity

The normalized identity along a retraction proves the original diagonal
law, using the prescribed pullback unit and composition comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeIndependentPairNormalization
open SheafPullbackPathComparison SchemeOverlapDiagonalChart SchemeModulePullbackUnits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y Z : Scheme.{u}}

/-- Identity after normalization implies the original sheaf diagonal equation. -/
theorem diagonal_of_normalize_refl (l r : Z ⟶ Y) (d : Y ⟶ Z)
    (hl : d ≫ l = 𝟙 Y) (hr : d ≫ r = 𝟙 Y) (M : Y.Modules)
    (e : (pullback l).obj M ≅ (pullback r).obj M)
    (h : normalize l r d (𝟙 Y) (𝟙 Y) hl hr M M e = Iso.refl _) :
    DiagonalCompatible l r d hl hr M e := by
  have hh := congrArg Iso.hom h
  have hc := congrArg (fun a ↦ (comparison d l (𝟙 Y) hl).hom.app M ≫ a ≫
    (pullbackId Y).hom.app M) hh
  dsimp only [normalize, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Iso.refl_hom] at hc
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Category.id_comp] at hc
  exact hc

end FLT.Mazur.SchemeIndependentPairNormalization

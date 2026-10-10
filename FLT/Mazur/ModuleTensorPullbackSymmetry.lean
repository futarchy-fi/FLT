/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleLineBundleTensorPullback
public import FLT.Mazur.ModuleSheafTensorAssociator

/-!
# Pullback preserves the actual tensor symmetry

The comparison is proved on original adjunction-unit sections. It gives
the transposed evaluation identity needed for biduality under base change.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.FCurve.ModuleLineBundleTensorPullback
open ModuleSheafTensor ModuleSheafTensorAssociator
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] tensor tensorIso ModuleSheafTensorAssociator.comm
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules)

/-- The canonical tensor pullback comparison commutes with transposition. -/
@[reassoc]
lemma tensorIso_comm :
    (tensorIso f M N).hom ≫
        (ModuleSheafTensorAssociator.comm ((pullback f).obj M) ((pullback f).obj N)).hom =
      (pullback f).map (ModuleSheafTensorAssociator.comm M N).hom ≫ (tensorIso f N M).hom := by
  let adj := pullbackPushforwardAdjunction f
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left]
  apply ModuleSheafTensor.hom_ext
  intro U m n
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, pushforward_map_app]
  erw [tensorIso_adj_pure f M N U m n]
  erw [comm_hom_pure, comm_hom_pure]
  exact (tensorIso_adj_pure f N M U n m).symm

end FLT.Mazur.FCurve.ModuleLineBundleTensorPullback

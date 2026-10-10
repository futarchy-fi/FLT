/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorPullbackComposition

/-!
# Identity coherence of tensor pullback

The prescribed identity comparison preserves the actual sheaf tensor pairing.
The proof uses adjunction units on arbitrary opens, without unfolding tensors.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve.ModuleLineBundleTensorPullback
open ModuleSheafTensor
attribute [local irreducible] tensor tensorIso
variable {X : Scheme.{u}}

/-- The identity comparison cancels the adjunction unit on every open. -/
lemma pullbackId_unit_open (M : X.Modules) (U : X.Opens) (m : Γ(M, U)) :
    ((pullbackId X).hom.app M).app U
      (((pullbackPushforwardAdjunction (𝟙 X)).unit.app M).app U m) = m := by
  have h := unit_conjugateEquiv Adjunction.id
    (pullbackPushforwardAdjunction (𝟙 X)) (pullbackId X).hom M
  rw [conjugateEquiv_pullbackId_hom] at h
  exact (congrArg (fun k ↦ k.app U m) h).symm

/-- The actual tensor comparison commutes with the prescribed identity pullback. -/
@[reassoc]
lemma tensorIso_id (M N : X.Modules) :
    (tensorIso (𝟙 X) M N).hom ≫
      map ((pullbackId X).hom.app M) ((pullbackId X).hom.app N) =
        (pullbackId X).hom.app (tensor M N) := by
  apply ((pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _).injective
  apply ModuleSheafTensor.hom_ext
  intro U m n
  change (map ((pullbackId X).hom.app M) ((pullbackId X).hom.app N)).app U
    ((tensorIso (𝟙 X) M N).hom.app U
      (((pullbackPushforwardAdjunction (𝟙 X)).unit.app (tensor M N)).app U
        (pure M N U m n))) = _
  have h := tensorIso_adj_pure (𝟙 X) M N U m n
  change (tensorIso (𝟙 X) M N).hom.app U
    (((pullbackPushforwardAdjunction (𝟙 X)).unit.app (tensor M N)).app U
      (pure M N U m n)) = _ at h
  rw [h]
  erw [map_pure, pullbackId_unit_open, pullbackId_unit_open]
  exact (pullbackId_unit_open (tensor M N) U (pure M N U m n)).symm

end FLT.Mazur.FCurve.ModuleLineBundleTensorPullback

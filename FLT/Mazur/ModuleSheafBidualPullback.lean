/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleTensorPullbackSymmetry
public import FLT.Mazur.ModuleSheafBidual
public import FLT.Mazur.ModuleSheafDualPullback

/-!
# Canonical biduality commutes with geometric pullback

The comparison is proved from evaluation and the actual tensor pullback
symmetry. No frame, chosen basis, or rank assumption is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.FCurve
open ModuleSheafTensor ModuleSheafTensorAssociator ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor tensorIso moduleSheafBidual moduleSheafDualPullbackHom
  ModuleSheafTensorAssociator.comm
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)

/-- Canonical biduality is the transpose of the original evaluation pairing. -/
lemma moduleSheafBidual_evaluation :
    map (moduleSheafBidual M) (𝟙 _) ≫ moduleSheafDualEvaluation (moduleSheafDual M) =
      (ModuleSheafTensorAssociator.comm M (moduleSheafDual M)).hom ≫
        moduleSheafDualEvaluation M := by
  apply ModuleSheafTensor.hom_ext
  intro U s φ
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, map_pure, Hom.id_app,
    ConcreteCategory.id_apply, moduleSheafDualEvaluation_pure, moduleSheafBidual_eval,
    comm_hom_pure]

/-- Pulling bidual evaluation gives the transposed original pulled pairing. -/
lemma moduleDualPullbackPairing_bidual :
    map ((pullback f).map (moduleSheafBidual M)) (𝟙 _) ≫
        moduleDualPullbackPairing f (moduleSheafDual M) =
      (ModuleSheafTensorAssociator.comm ((pullback f).obj M)
        ((pullback f).obj (moduleSheafDual M))).hom ≫
        moduleDualPullbackPairing f M := by
  apply (cancel_epi (tensorIso f M (moduleSheafDual M)).hom).mp
  have hn := tensorIso_naturality f (moduleSheafBidual M) (𝟙 (moduleSheafDual M))
  erw [CategoryTheory.Functor.map_id] at hn
  simp only [moduleDualPullbackPairing]
  rw [← reassoc_of% hn, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc,
    moduleSheafBidual_evaluation, Functor.map_comp, Category.assoc,
    tensorIso_comm_assoc, Iso.hom_inv_id_assoc]

/-- The actual dual pullback comparisons intertwine the canonical bidual maps. -/
lemma moduleSheafBidual_pullback :
    (pullback f).map (moduleSheafBidual M) ≫
        moduleSheafDualPullbackHom f (moduleSheafDual M) =
      moduleSheafBidual ((pullback f).obj M) ≫
        moduleSheafDualMap ((pullback f).obj (moduleSheafDual M))
          (moduleSheafDualPullbackHom f M) := by
  apply moduleSheafDual_hom_ext
  rw [show map ((pullback f).map (moduleSheafBidual M) ≫
      moduleSheafDualPullbackHom f (moduleSheafDual M)) (𝟙 _) =
      map ((pullback f).map (moduleSheafBidual M)) (𝟙 _) ≫
        map (moduleSheafDualPullbackHom f (moduleSheafDual M)) (𝟙 _) by
    rw [← map_comp, Category.id_comp]]
  rw [Category.assoc, moduleSheafDualPullbackHom_evaluation,
    moduleDualPullbackPairing_bidual]
  apply ModuleSheafTensor.hom_ext
  intro U s φ
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, map_pure, Hom.id_app,
    ConcreteCategory.id_apply, comm_hom_pure, moduleSheafDualEvaluation_pure,
    moduleSheafDualMap_app, moduleDualEval_precomp, moduleSheafBidual_eval,
    moduleSheafDualPullbackHom_eval]

end FLT.Mazur.FCurve

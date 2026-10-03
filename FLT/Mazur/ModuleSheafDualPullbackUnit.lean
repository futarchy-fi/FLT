/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafDualPullback

/-!
# Unit and section compatibility of dual pullback

The canonical comparison is invertible for the structure module and every
globally trivial module. Transport along an actual module isomorphism retains
the evaluation pairing and the dual of an inclusion into the structure module.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}}

/-- Evaluation for the structure module is scalar multiplication. -/
lemma moduleSheafDualEvaluation_unit :
    moduleSheafDualEvaluation (structureModule X) =
      ModuleSheafTensor.map (moduleSheafDualUnitIso (X := X)).hom (𝟙 _) ≫
        (ModuleSheafTensor.leftUnitor (structureModule X)).hom := by
  apply ModuleSheafTensor.hom_ext
  intro U φ s
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, ModuleSheafTensor.map_pure,
    Hom.id_app, ConcreteCategory.id_apply, moduleSheafDualEvaluation_pure]
  erw [ModuleSheafTensor.leftUnitor_pure]
  change Γ(X, U) at s
  change moduleDualEval (structureModule X) U φ s =
    moduleDualEval (structureModule X) U φ (1 : Γ(X, U)) * s
  conv_lhs => rw [← moduleDualUnitSection_eval U φ]
  exact moduleDualEval_unitSection U _ s

/-- The explicit invertible comparison for the dual of the structure module. -/
def moduleDualPullbackUnitIso (f : X ⟶ Y) :
    (pullback f).obj (moduleSheafDual (structureModule Y)) ≅
      moduleSheafDual ((pullback f).obj (structureModule Y)) :=
  (pullback f).mapIso moduleSheafDualUnitIso ≪≫ modulePullbackUnitIso f ≪≫
    moduleSheafDualUnitIso.symm ≪≫
      moduleSheafDualIso _ (modulePullbackUnitIso f)

/-- The pulled-back unit pairing is multiplication followed by the unit comparison. -/
lemma moduleDualPullbackPairing_unit_object (f : X ⟶ Y) :
    moduleDualPullbackPairing f (structureModule Y) =
      ModuleSheafTensor.map ((pullback f).map moduleSheafDualUnitIso.hom ≫
        (modulePullbackUnitIso f).hom) (𝟙 _) ≫
      (ModuleSheafTensor.leftUnitor ((pullback f).obj (structureModule Y))).hom ≫
        (modulePullbackUnitIso f).hom := by
  rw [← cancel_epi (ModuleLineBundleTensorPullback.tensorIso f
    (moduleSheafDual (structureModule Y)) (structureModule Y)).hom]
  simp only [moduleDualPullbackPairing, Iso.hom_inv_id_assoc]
  rw [moduleSheafDualEvaluation_unit, Functor.map_comp]
  have hn := ModuleLineBundleTensorPullback.tensorIso_naturality f
    (moduleSheafDualUnitIso (X := Y)).hom (𝟙 (structureModule Y))
  erw [CategoryTheory.Functor.map_id] at hn
  rw [← Category.id_comp (𝟙 ((pullback f).obj (structureModule Y))),
    ModuleSheafTensor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hn,
    reassoc_of% ModuleLineBundleTensorPullback.tensorIso_leftUnitor f (structureModule Y)]

set_option maxHeartbeats 600000 in
-- Evaluation unfolds the four factors of the unit comparison.
/-- The explicit unit isomorphism equals the canonical dual comparison. -/
lemma moduleDualPullbackUnitIso_hom (f : X ⟶ Y) :
    (moduleDualPullbackUnitIso f).hom = moduleSheafDualPullbackHom f (structureModule Y) := by
  apply moduleSheafDualHom_ext
  rw [moduleSheafDualPullbackHom_evaluation, moduleDualPullbackPairing_unit_object]
  apply ModuleSheafTensor.hom_ext
  intro U φ s
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, ModuleSheafTensor.map_pure,
    Hom.id_app, ConcreteCategory.id_apply, moduleSheafDualEvaluation_pure]
  erw [ModuleSheafTensor.leftUnitor_pure]
  change moduleDualEval ((pullback f).obj (structureModule Y)) U
    ((Scheme.Modules.restrictFunctor U.ι).map (modulePullbackUnitIso f).hom ≫
      moduleDualUnitSection U
        ((modulePullbackUnitIso f).hom.app U
          (((pullback f).map moduleSheafDualUnitIso.hom).app U φ))) s = _
  rw [moduleDualEval_precomp, moduleDualEval_unitSection]
  exact ((modulePullbackUnitIso f).hom.app_smul _ s).symm

/-- The canonical comparison is invertible on the structure module. -/
instance moduleSheafDualPullbackHom_unit_isIso (f : X ⟶ Y) :
    IsIso (moduleSheafDualPullbackHom f (structureModule Y)) := by
  rw [← moduleDualPullbackUnitIso_hom]
  infer_instance

/-- The canonical comparison is invertible on every globally trivial module. -/
lemma moduleSheafDualPullbackHom_isIso_of_trivial (f : X ⟶ Y) {M : Y.Modules}
    (e : M ≅ structureModule Y) : IsIso (moduleSheafDualPullbackHom f M) := by
  have : IsIso (moduleSheafDualMap M e.hom) :=
    inferInstanceAs (IsIso (moduleSheafDualIso M e).hom)
  have : IsIso (moduleSheafDualMap ((pullback f).obj M) ((pullback f).map e.hom)) :=
    inferInstanceAs (IsIso (moduleSheafDualIso _ ((pullback f).mapIso e)).hom)
  have : IsIso ((pullback f).map (moduleSheafDualMap M e.hom) ≫
      moduleSheafDualPullbackHom f M) := by
    rw [moduleSheafDualPullbackHom_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left ((pullback f).map (moduleSheafDualMap M e.hom)) _

/-- Dualizing a map into the structure module commutes with pullback. -/
lemma moduleSheafDualPullbackHom_section (f : X ⟶ Y) {M : Y.Modules}
    (a : M ⟶ structureModule Y) :
    (pullback f).map (moduleSheafDualUnitIso.inv ≫ moduleSheafDualMap M a) ≫
      moduleSheafDualPullbackHom f M =
    (modulePullbackUnitIso f).hom ≫ moduleSheafDualUnitIso.inv ≫
      moduleSheafDualMap ((pullback f).obj M)
        ((pullback f).map a ≫ (modulePullbackUnitIso f).hom) := by
  rw [Functor.map_comp, Category.assoc, moduleSheafDualPullbackHom_naturality,
    ← moduleDualPullbackUnitIso_hom]
  dsimp only [moduleDualPullbackUnitIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, moduleSheafDualIso]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, moduleSheafDualMap_comp]

/-- Transport the dual pullback comparison through an actual module isomorphism. -/
def moduleSheafDualPullbackViaIso (f : X ⟶ Y) (M : Y.Modules) {N : X.Modules}
    (e : (pullback f).obj M ≅ N) :
    (pullback f).obj (moduleSheafDual M) ⟶ moduleSheafDual N :=
  moduleSheafDualPullbackHom f M ≫ (moduleSheafDualIso _ e).inv

/-- Transport preserves evaluation on corresponding module sections. -/
lemma moduleSheafDualPullbackViaIso_eval (f : X ⟶ Y) (M : Y.Modules) {N : X.Modules}
    (e : (pullback f).obj M ≅ N) (U : X.Opens)
    (φ : Γ((pullback f).obj (moduleSheafDual M), U)) (s : Γ((pullback f).obj M, U)) :
    moduleDualEval N U ((moduleSheafDualPullbackViaIso f M e).app U φ)
      (e.hom.app U s) =
      (moduleDualPullbackPairing f M).app U (ModuleSheafTensor.pure _ _ U φ s) := by
  change moduleDualEval N U ((restrictFunctor U.ι).map e.inv ≫
    (moduleSheafDualPullbackHom f M).app U φ) (e.hom.app U s) = _
  rw [moduleDualEval_precomp]
  have he := congrArg (fun k ↦ k.app U s) e.hom_inv_id
  change e.inv.app U (e.hom.app U s) = s at he
  rw [he]
  exact moduleSheafDualPullbackHom_eval f M U φ s

/-- An isomorphism respecting inclusions also respects their dual sections. -/
lemma moduleSheafDualPullbackViaIso_section (f : X ⟶ Y) {M : Y.Modules} {N : X.Modules}
    (e : (pullback f).obj M ≅ N) (a : M ⟶ structureModule Y)
    (b : N ⟶ structureModule X)
    (he : e.hom ≫ b = (pullback f).map a ≫ (modulePullbackUnitIso f).hom) :
    (pullback f).map (moduleSheafDualUnitIso.inv ≫ moduleSheafDualMap M a) ≫
      moduleSheafDualPullbackViaIso f M e =
      (modulePullbackUnitIso f).hom ≫ moduleSheafDualUnitIso.inv ≫ moduleSheafDualMap N b := by
  dsimp only [moduleSheafDualPullbackViaIso, moduleSheafDualIso]
  rw [← Category.assoc, moduleSheafDualPullbackHom_section]
  simp only [Category.assoc]
  rw [← moduleSheafDualMap_comp, ← he, Iso.inv_hom_id_assoc]

end FLT.Mazur.FCurve

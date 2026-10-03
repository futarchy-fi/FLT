/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafDualInternalHom
public import FLT.Mazur.ModuleLineBundleTensorPullback
public import FLT.Mazur.ModulePullbackUnitCoherence

/-!
# The canonical pullback map for dual module sheaves

Pulling back the actual tensor evaluation and currying gives a canonical
comparison. Its pairing agrees with pullback on adjunction-unit sections and
is natural in the original module. Invertibility needs a separate argument.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)

/-- Pullback of the actual dual evaluation, through the tensor comparison. -/
def moduleDualPullbackPairing :
    ModuleSheafTensor.tensor ((pullback f).obj (moduleSheafDual M))
      ((pullback f).obj M) ⟶ structureModule X :=
  (ModuleLineBundleTensorPullback.tensorIso f (moduleSheafDual M) M).inv ≫
    (pullback f).map (moduleSheafDualEvaluation M) ≫ (modulePullbackUnitIso f).hom

/-- The canonical comparison from pullback of a dual to the dual of a pullback. -/
def moduleSheafDualPullbackHom :
    (pullback f).obj (moduleSheafDual M) ⟶ moduleSheafDual ((pullback f).obj M) :=
  ModuleSheafTensorCurrying.homEquiv _ _ _ (moduleDualPullbackPairing f M) ≫
    (moduleSheafDualInternalHomIso ((pullback f).obj M)).inv

/-- The comparison preserves the actual tensor evaluation pairing. -/
@[reassoc]
lemma moduleSheafDualPullbackHom_evaluation :
    ModuleSheafTensor.map (moduleSheafDualPullbackHom f M) (𝟙 _) ≫
      moduleSheafDualEvaluation ((pullback f).obj M) = moduleDualPullbackPairing f M := by
  rw [moduleSheafDualEvaluation, ← ModuleSheafTensorCurrying.homEquiv_symm_precomp]
  change (ModuleSheafTensorCurrying.homEquiv _ _ _).symm
    ((ModuleSheafTensorCurrying.homEquiv _ _ _ (moduleDualPullbackPairing f M) ≫
      (moduleSheafDualInternalHomIso _).inv) ≫ (moduleSheafDualInternalHomIso _).hom) = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Equiv.symm_apply_apply]

/-- Evaluation of the comparison on arbitrary source sections. -/
lemma moduleSheafDualPullbackHom_eval (U : X.Opens)
    (φ : Γ((pullback f).obj (moduleSheafDual M), U)) (s : Γ((pullback f).obj M, U)) :
    moduleDualEval ((pullback f).obj M) U ((moduleSheafDualPullbackHom f M).app U φ) s =
      (moduleDualPullbackPairing f M).app U (ModuleSheafTensor.pure _ _ U φ s) := by
  have h := congrArg (fun k ↦ k.app U (ModuleSheafTensor.pure _ _ U φ s))
    (moduleSheafDualPullbackHom_evaluation f M)
  simpa only [Hom.comp_app, ConcreteCategory.comp_apply, ModuleSheafTensor.map_pure,
    Hom.id_app, ConcreteCategory.id_apply, moduleSheafDualEvaluation_pure] using h

/-- On sections from the adjunction units, the pairing is the pulled-back function. -/
lemma moduleDualPullbackPairing_unit (U : Y.Opens) (φ : ModuleDualSections M U)
    (s : Γ(M, U)) :
    (moduleDualPullbackPairing f M).app (f ⁻¹ᵁ U)
      (ModuleSheafTensor.pure _ _ (f ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction f).unit.app (moduleSheafDual M)).app U φ)
        (((pullbackPushforwardAdjunction f).unit.app M).app U s)) =
      f.app U (moduleDualEval M U φ s) := by
  have ht := ModuleLineBundleTensorPullback.tensorIso_adj_pure f
    (moduleSheafDual M) M U φ s
  have hn := congrArg (fun k ↦ k.app U (ModuleSheafTensor.pure _ _ U φ s))
    ((pullbackPushforwardAdjunction f).unit.naturality (moduleSheafDualEvaluation M)).symm
  have hi := congrArg (fun z ↦
    (ModuleLineBundleTensorPullback.tensorIso f (moduleSheafDual M) M).inv.app (f ⁻¹ᵁ U) z) ht
  have he := congrArg (fun k ↦ k.app (f ⁻¹ᵁ U)
    (((pullbackPushforwardAdjunction f).unit.app
      (ModuleSheafTensor.tensor (moduleSheafDual M) M)).app U
        (ModuleSheafTensor.pure _ _ U φ s)))
    (ModuleLineBundleTensorPullback.tensorIso f (moduleSheafDual M) M).hom_inv_id
  exact (congrArg (fun z ↦ (modulePullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
    (((pullback f).map (moduleSheafDualEvaluation M)).app (f ⁻¹ᵁ U) z))
      (hi.symm.trans he)).trans
    ((congrArg ((modulePullbackUnitIso f).hom.app (f ⁻¹ᵁ U)) hn).trans
      ((modulePullbackUnitIso_unit f U _).trans
        (congrArg (f.app U) (moduleSheafDualEvaluation_pure M U φ s))))

/-- Maps into the dual are determined by their tensor evaluation pairings. -/
lemma moduleSheafDualHom_ext {L N : X.Modules} {a b : L ⟶ moduleSheafDual N}
    (h : ModuleSheafTensor.map a (𝟙 N) ≫ moduleSheafDualEvaluation N =
      ModuleSheafTensor.map b (𝟙 N) ≫ moduleSheafDualEvaluation N) : a = b := by
  apply (cancel_mono (moduleDualInternalHom N)).mp
  apply (ModuleSheafTensorCurrying.homEquiv L N (structureModule X)).symm.injective
  simpa only [moduleSheafDualEvaluation, ModuleSheafTensorCurrying.homEquiv_symm_precomp]
    using h

/-- The pulled-back pairing is natural in the original module. -/
lemma moduleDualPullbackPairing_naturality {N : Y.Modules} (a : M ⟶ N) :
    ModuleSheafTensor.map ((pullback f).map (moduleSheafDualMap M a)) (𝟙 _) ≫
      moduleDualPullbackPairing f M =
    ModuleSheafTensor.map (𝟙 _) ((pullback f).map a) ≫ moduleDualPullbackPairing f N := by
  rw [← cancel_epi (ModuleLineBundleTensorPullback.tensorIso f (moduleSheafDual N) M).hom]
  have h₁ := ModuleLineBundleTensorPullback.tensorIso_naturality f
    (moduleSheafDualMap M a) (𝟙 M)
  have h₂ := ModuleLineBundleTensorPullback.tensorIso_naturality f
    (𝟙 (moduleSheafDual N)) a
  erw [CategoryTheory.Functor.map_id] at h₁
  erw [CategoryTheory.Functor.map_id] at h₂
  simp only [moduleDualPullbackPairing]
  rw [← reassoc_of% h₁, ← reassoc_of% h₂]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    moduleSheafDualEvaluation_naturality]

/-- The canonical dual comparison is natural in the original module. -/
lemma moduleSheafDualPullbackHom_naturality {N : Y.Modules} (a : M ⟶ N) :
    (pullback f).map (moduleSheafDualMap M a) ≫ moduleSheafDualPullbackHom f M =
      moduleSheafDualPullbackHom f N ≫ moduleSheafDualMap ((pullback f).obj M)
        ((pullback f).map a) := by
  apply moduleSheafDualHom_ext
  rw [← Category.id_comp (𝟙 ((pullback f).obj M)), ModuleSheafTensor.map_comp,
    Category.assoc, moduleSheafDualPullbackHom_evaluation]
  rw [ModuleSheafTensor.map_comp, Category.assoc, moduleSheafDualEvaluation_naturality]
  rw [← Category.assoc, ← ModuleSheafTensor.map_comp]
  simp only [Category.comp_id, Category.id_comp]
  rw [show ModuleSheafTensor.map (moduleSheafDualPullbackHom f N) ((pullback f).map a) =
      ModuleSheafTensor.map (𝟙 _) ((pullback f).map a) ≫
        ModuleSheafTensor.map (moduleSheafDualPullbackHom f N) (𝟙 _) by
      rw [← ModuleSheafTensor.map_comp]; simp]
  rw [Category.assoc, moduleSheafDualPullbackHom_evaluation]
  exact moduleDualPullbackPairing_naturality f M a

end FLT.Mazur.FCurve

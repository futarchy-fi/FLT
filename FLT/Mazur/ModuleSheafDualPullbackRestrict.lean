/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafDualPullbackUnit
public import FLT.Mazur.ModuleSheafOpenIsoDetection
public import FLT.Mazur.ModuleTensorPullbackRestriction

/-!
# Canonical dual pullback on open charts

Restriction of the actual evaluation pairing proves compatibility of the
canonical dual-pullback morphism with the chosen open comparisons. On each
rank-one chart the comparison is invertible; open-cover detection then gives
the global isomorphism, without assuming invertibility of the morphism.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
namespace FLT.Mazur.FCurve
variable {X : Scheme.{u}}
/-- Restriction preserves the actual dual tensor evaluation. -/
lemma moduleSheafDualEvaluation_restrict (M : X.Modules) (U : X.Opens) :
    (ModuleSheafTensor.restrictIso (moduleSheafDual M) M U.ι).hom ≫
      ModuleSheafTensor.map (moduleSheafDualRestrictIso M U).hom (𝟙 _) ≫
      moduleSheafDualEvaluation (M.restrict U.ι) =
    (restrictFunctor U.ι).map (moduleSheafDualEvaluation M) ≫
      (restrictUnitIso U.ι).hom := by
  apply ModuleSheafTensor.restrict_hom_ext U.ι
  intro W φ s
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  rw [ModuleSheafTensor.restrictIso_hom_pure, ModuleSheafTensor.map_pure,
    moduleSheafDualEvaluation_pure]
  change moduleDualEval (M.restrict U.ι) W (moduleDualOpenSectionsEquiv M U W φ) s =
    (U.ι.appIso W).hom ((moduleSheafDualEvaluation M).app (U.ι ''ᵁ W)
      (ModuleSheafTensor.pure (moduleSheafDual M) M (U.ι ''ᵁ W) φ s))
  rw [Scheme.Opens.ι_appIso]
  change _ = (moduleSheafDualEvaluation M).app (U.ι ''ᵁ W)
    (ModuleSheafTensor.pure (moduleSheafDual M) M (U.ι ''ᵁ W) φ s)
  rw [moduleDualOpenSectionsEquiv_eval, moduleSheafDualEvaluation_pure]

variable {Y : Scheme.{u}}
/-- The canonical pulled-back pairing commutes with open restriction. -/
lemma moduleDualPullbackPairing_restrict (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) :
    (restrictFunctor (f ⁻¹ᵁ U).ι).map (moduleDualPullbackPairing f M) ≫
      (restrictUnitIso (f ⁻¹ᵁ U).ι).hom =
    (ModuleSheafTensor.restrictIso ((pullback f).obj (moduleSheafDual M))
      ((pullback f).obj M) (f ⁻¹ᵁ U).ι).hom ≫
      ModuleSheafTensor.map ((modulePullbackOpenIso f U (moduleSheafDual M)).hom ≫
        (pullback (f ∣_ U)).map (moduleSheafDualRestrictIso M U).hom)
        (modulePullbackOpenIso f U M).hom ≫
        moduleDualPullbackPairing (f ∣_ U) (M.restrict U.ι) := by
  rw [← cancel_epi ((restrictFunctor (f ⁻¹ᵁ U).ι).map
    (ModuleLineBundleTensorPullback.tensorIso f (moduleSheafDual M) M).hom)]
  simp only [moduleDualPullbackPairing, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Category.comp_id (modulePullbackOpenIso f U M).hom, ModuleSheafTensor.map_comp]
  simp only [Category.assoc]
  dsimp only [modulePullbackOpenIso]
  rw [reassoc_of% ModuleLineBundleTensorPullback.tensorIso_restrictSquare f (f ∣_ U)
    (f ⁻¹ᵁ U).ι U.ι (morphismRestrict_ι f U).symm (moduleSheafDual M) M]
  have hn := ModuleLineBundleTensorPullback.tensorIso_naturality (f ∣_ U)
    (moduleSheafDualRestrictIso M U).hom (𝟙 (M.restrict U.ι))
  erw [CategoryTheory.Functor.map_id] at hn
  rw [← reassoc_of% hn]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc (pullback (f ∣_ U)),
    ← Functor.map_comp_assoc (pullback (f ∣_ U))]
  simp only [Category.assoc]
  rw [moduleSheafDualEvaluation_restrict M U, Functor.map_comp]
  simp only [Category.assoc]
  rw [← modulePullbackRestrictIso_naturality_assoc f (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι
    (morphismRestrict_ι f U).symm (moduleSheafDualEvaluation M)]
  rw [modulePullbackRestrictIso_unit]


set_option maxRecDepth 2048 in
-- Comparing the nested restrictions requires unfolding their scalar transports.
/-- The dual-pullback morphism respects the chosen open comparisons. -/
lemma moduleSheafDualPullbackHom_restrict (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) :
    (restrictFunctor (f ⁻¹ᵁ U).ι).map (moduleSheafDualPullbackHom f M) ≫
      (moduleSheafDualRestrictIso ((pullback f).obj M) (f ⁻¹ᵁ U)).hom =
    (modulePullbackOpenIso f U (moduleSheafDual M)).hom ≫
      (pullback (f ∣_ U)).map (moduleSheafDualRestrictIso M U).hom ≫
      moduleSheafDualPullbackHom (f ∣_ U) (M.restrict U.ι) ≫
      moduleSheafDualMap (((pullback f).obj M).restrict (f ⁻¹ᵁ U).ι)
        (modulePullbackOpenIso f U M).hom := by
  apply moduleSheafDualHom_ext
  rw [← cancel_epi (ModuleSheafTensor.restrictIso
    ((pullback f).obj (moduleSheafDual M)) ((pullback f).obj M) (f ⁻¹ᵁ U).ι).hom]
  apply ModuleSheafTensor.restrict_hom_ext (f ⁻¹ᵁ U).ι
  intro W φ s
  simp only [Hom.comp_app, ConcreteCategory.comp_apply,
    ModuleSheafTensor.restrictIso_hom_pure, ModuleSheafTensor.map_pure,
    moduleSheafDualEvaluation_pure, Hom.id_app, ConcreteCategory.id_apply]
  change moduleDualEval (((pullback f).obj M).restrict (f ⁻¹ᵁ U).ι) W
      (moduleDualOpenSectionsEquiv ((pullback f).obj M) (f ⁻¹ᵁ U) W
        ((moduleSheafDualPullbackHom f M).app ((f ⁻¹ᵁ U).ι ''ᵁ W) φ)) s =
    moduleDualEval (((pullback f).obj M).restrict (f ⁻¹ᵁ U).ι) W
      ((restrictFunctor W.ι).map (modulePullbackOpenIso f U M).hom ≫
        (moduleSheafDualPullbackHom (f ∣_ U) (M.restrict U.ι)).app W
          (((pullback (f ∣_ U)).map (moduleSheafDualRestrictIso M U).hom).app W
            ((modulePullbackOpenIso f U (moduleSheafDual M)).hom.app W φ))) s
  rw [moduleDualOpenSectionsEquiv_eval, moduleSheafDualPullbackHom_eval,
    moduleDualEval_precomp, moduleSheafDualPullbackHom_eval]
  have hp := congrArg (fun k ↦ k.app W
    (((ModuleSheafTensor.tensor ((pullback f).obj (moduleSheafDual M))
      ((pullback f).obj M)).restrictAppIso (f ⁻¹ᵁ U).ι W).inv
      (ModuleSheafTensor.pure _ _ ((f ⁻¹ᵁ U).ι ''ᵁ W) φ s)))
    (moduleDualPullbackPairing_restrict f M U)
  simp only [Hom.comp_app, ConcreteCategory.comp_apply,
    ModuleSheafTensor.restrictIso_hom_pure, ModuleSheafTensor.map_pure] at hp
  change ((f ⁻¹ᵁ U).ι.appIso W).hom _ = _ at hp
  rw [Scheme.Opens.ι_appIso] at hp
  exact hp

/-- Open restriction commutes with canonical dual pullback on both sides. -/
lemma moduleSheafDualPullbackHom_open (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) :
    (restrictFunctor (f ⁻¹ᵁ U).ι).map (moduleSheafDualPullbackHom f M) ≫
      (moduleSheafDualRestrictIso ((pullback f).obj M) (f ⁻¹ᵁ U)).hom ≫
      (moduleSheafDualIso _ (modulePullbackOpenIso f U M)).inv =
    (modulePullbackOpenIso f U (moduleSheafDual M)).hom ≫
      (pullback (f ∣_ U)).map (moduleSheafDualRestrictIso M U).hom ≫
      moduleSheafDualPullbackHom (f ∣_ U) (M.restrict U.ι) := by
  rw [← Category.assoc, moduleSheafDualPullbackHom_restrict]
  change (_ ≫ _ ≫ _ ≫ (moduleSheafDualIso _ (modulePullbackOpenIso f U M)).hom) ≫
    (moduleSheafDualIso _ (modulePullbackOpenIso f U M)).inv = _
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Canonical dual pullback is invertible for locally free rank-one modules. -/
lemma moduleSheafDualPullbackHom_isIso_of_locallyFreeRankOne
    (f : X ⟶ Y) {M : Y.Modules} (hM : LocallyFreeRankOne M) :
    IsIso (moduleSheafDualPullbackHom f M) := by
  choose U hU he using hM
  apply ModuleSheafOpenIsoDetection.isIso_of_openCover _ (fun y ↦ f ⁻¹ᵁ U y)
    (fun x ↦ ⟨f x, hU (f x)⟩)
  intro y
  have := moduleSheafDualPullbackHom_isIso_of_trivial (f ∣_ U y) (Classical.choice (he y))
  have : IsIso ((restrictFunctor (f ⁻¹ᵁ U y).ι).map (moduleSheafDualPullbackHom f M) ≫
      (moduleSheafDualRestrictIso ((pullback f).obj M) (f ⁻¹ᵁ U y)).hom ≫
      (moduleSheafDualIso _ (modulePullbackOpenIso f (U y) M)).inv) := by
    rw [moduleSheafDualPullbackHom_open]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((moduleSheafDualRestrictIso ((pullback f).obj M) (f ⁻¹ᵁ U y)).hom ≫
      (moduleSheafDualIso _ (modulePullbackOpenIso f (U y) M)).inv)

/-- Pullback of a locally free rank-one dual is canonically the dual pullback. -/
def moduleSheafDualPullbackIso (f : X ⟶ Y) {M : Y.Modules} (hM : LocallyFreeRankOne M) :
    (pullback f).obj (moduleSheafDual M) ≅ moduleSheafDual ((pullback f).obj M) := by
  letI := moduleSheafDualPullbackHom_isIso_of_locallyFreeRankOne f hM
  exact asIso (moduleSheafDualPullbackHom f M)

/-- The isomorphism uses the original canonical comparison morphism. -/
@[simp]
lemma moduleSheafDualPullbackIso_hom (f : X ⟶ Y) {M : Y.Modules}
    (hM : LocallyFreeRankOne M) :
    (moduleSheafDualPullbackIso f hM).hom = moduleSheafDualPullbackHom f M := rfl

end FLT.Mazur.FCurve

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionDivisorNeutralTwist
public import FLT.Mazur.CartierAbelDirectImageSections

/-!
# Removing the neutral twist from the actual direct-image map

The tensor-duality map for the neutral base line agrees with the ordinary
pullback-pushforward adjoint of the original section. All unit comparisons
are retained, so this identifies the canonical section rather than a scalar
multiple of an unspecified frame.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor lineHomSectionEquiv


variable {X S : Scheme} (f : X ⟶ S) (L : X.Modules)

/-- On actual pure sections the neutral comparison is scalar multiplication. -/
theorem sectionNeutralTwistIso_pure (U : X.Opens) (l : Γ(L, U))
    (b : Γ((pullback f).obj (structureModule S), U)) :
    (sectionNeutralTwistIso f L).hom.app U (pure L _ U l b) =
      (show Γ(X, U) from (modulePullbackUnitIso f).hom.app U b) • l := by
  exact (congrArg ((rightUnitor L).hom.app U)
    (map_pure (𝟙 L) (modulePullbackUnitIso f).hom U l b)).trans
      (rightUnitor_pure L U ((modulePullbackUnitIso f).hom.app U b) l)

attribute [local irreducible] sectionNeutralTwistIso

/-- Contraction of the neutral twist is natural in its coefficient sheaf. -/
theorem sectionNeutralTwistIso_naturality {M : X.Modules} (a : L ⟶ M) :
    map a (𝟙 ((pullback f).obj (structureModule S))) ≫
        (sectionNeutralTwistIso f M).hom =
      (sectionNeutralTwistIso f L).hom ≫ a := by
  apply ModuleSheafTensor.hom_ext
  intro U l b
  exact (congrArg ((sectionNeutralTwistIso f M).hom.app U)
    (map_pure a (𝟙 _) U l b)).trans
      ((sectionNeutralTwistIso_pure f M U (a.app U l) b).trans
        ((a.app_smul _ l).symm.trans
          (congrArg (a.app U) (sectionNeutralTwistIso_pure f L U l b).symm)))

/-- The pulled dual evaluation contracts the neutral twist by its actual unit map. -/
theorem neutral_dual_contraction :
    map (moduleSheafDualPullbackIso f structureModule_locallyFreeRankOne).hom (𝟙 _) ≫
        (lineSheafDualEvaluationIso
          (structureModule_locallyFreeRankOne.pullback f)).hom =
      map ((pullback f).map moduleSheafDualUnitIso.hom ≫
        (modulePullbackUnitIso f).hom) (𝟙 _) ≫
          (sectionNeutralTwistIso f (structureModule X)).hom := by
  change map (moduleSheafDualPullbackHom f (structureModule S)) (𝟙 _) ≫
    moduleSheafDualEvaluation _ = _
  rw [moduleSheafDualPullbackHom_evaluation, moduleDualPullbackPairing_unit_object]
  apply ModuleSheafTensor.hom_ext
  intro U a b
  let u := (pullback f).map moduleSheafDualUnitIso.hom ≫ (modulePullbackUnitIso f).hom
  have hl := congrArg ((modulePullbackUnitIso f).hom.app U)
    (leftUnitor_pure ((pullback f).obj (structureModule S)) U (u.app U a) b)
  have hr := (congrArg ((sectionNeutralTwistIso f (structureModule X)).hom.app U)
    (map_pure u (𝟙 _) U a b)).trans
      (sectionNeutralTwistIso_pure f (structureModule X) U (u.app U a) b)
  have hc : (show Γ(X, U) from u.app U a) • (modulePullbackUnitIso f).hom.app U b =
      (show Γ(X, U) from (modulePullbackUnitIso f).hom.app U b) • u.app U a := by
    exact mul_comm (show Γ(X, U) from u.app U a)
      (show Γ(X, U) from (modulePullbackUnitIso f).hom.app U b)
  have hl₀ := congrArg (fun z ↦ (modulePullbackUnitIso f).hom.app U
    ((leftUnitor ((pullback f).obj (structureModule S))).hom.app U z))
      (map_pure u (𝟙 _) U a b)
  exact hl₀.trans (hl.trans
    (((modulePullbackUnitIso f).hom.app_smul _ b).trans (hc.trans hr.symm)))

/-- The original section's ordinary adjoint, with no choice of frames. -/
def sectionDirectImageMap (s : Γ(L, ⊤)) :
    structureModule S ⟶ (pushforward f).obj L :=
  (pullbackPushforwardAdjunction f).homEquiv _ _
    ((modulePullbackUnitIso f).hom ≫ globalSectionHom L s)

/-- Removing the neutral twist retains the original total-space adjoint. -/
theorem neutralTwist_adjoint (s : Γ(L, ⊤)) :
    (moduleSheafDualPullbackIso f structureModule_locallyFreeRankOne).hom ≫
        (lineHomSectionEquiv L (structureModule_locallyFreeRankOne.pullback f)).symm
          ((sectionNeutralTwistIso f L).inv.app ⊤ s) =
      (pullback f).map moduleSheafDualUnitIso.hom ≫
        (modulePullbackUnitIso f).hom ≫ globalSectionHom L s := by
  apply (lineTensorEquivalence
    (structureModule_locallyFreeRankOne.pullback f)).functor.map_injective
  change map _ (𝟙 _) = map _ (𝟙 _)
  apply (cancel_mono (sectionNeutralTwistIso f L).hom).mp
  let d := (moduleSheafDualPullbackIso f structureModule_locallyFreeRankOne).hom
  let b := (lineHomSectionEquiv L (structureModule_locallyFreeRankOne.pullback f)).symm
    ((sectionNeutralTwistIso f L).inv.app ⊤ s)
  let u := (pullback f).map moduleSheafDualUnitIso.hom ≫ (modulePullbackUnitIso f).hom
  let v := (lineSheafDualEvaluationIso
    (structureModule_locallyFreeRankOne.pullback f)).hom
  have he : (sectionNeutralTwistIso f L).hom.app ⊤
      ((sectionNeutralTwistIso f L).inv.app ⊤ s) = s :=
    ConcreteCategory.congr_hom
      (congrArg (fun a ↦ a.app ⊤) (sectionNeutralTwistIso f L).inv_hom_id) s
  have hn := (globalSectionHom_naturality _ (sectionNeutralTwistIso f L).hom
    ((sectionNeutralTwistIso f L).inv.app ⊤ s)).trans (congrArg (globalSectionHom L) he)
  calc
    map (d ≫ b) (𝟙 _) ≫ (sectionNeutralTwistIso f L).hom =
        map d (𝟙 _) ≫ (map b (𝟙 _) ≫ (sectionNeutralTwistIso f L).hom) := by
      rw [← Category.assoc, ← map_comp, Category.id_comp]
    _ = map d (𝟙 _) ≫ v ≫ globalSectionHom L s := by
      have hb := lineHomSectionEquiv_symm_tensor L
        (structureModule_locallyFreeRankOne.pullback f)
        ((sectionNeutralTwistIso f L).inv.app ⊤ s)
      exact congrArg (fun a ↦ map d (𝟙 _) ≫ a)
        ((congrArg (fun a ↦ a ≫ (sectionNeutralTwistIso f L).hom) hb).trans
          ((Category.assoc _ _ _).trans (congrArg (fun a ↦ v ≫ a) hn)))
    _ = map u (𝟙 _) ≫ (sectionNeutralTwistIso f (structureModule X)).hom ≫
        globalSectionHom L s := by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun a ↦ a ≫ globalSectionHom L s) (neutral_dual_contraction f)).trans
          (Category.assoc _ _ _))
    _ = map (u ≫ globalSectionHom L s) (𝟙 _) ≫ (sectionNeutralTwistIso f L).hom := by
      rw [← sectionNeutralTwistIso_naturality, ← Category.assoc, ← map_comp,
        Category.id_comp]
      rfl
    _ = _ := by
      rw [Category.assoc]
      rfl

/-- Tensor duality for a neutral twist equals the ordinary original-section adjunction. -/
theorem neutralTwist_directImage (s : Γ(L, ⊤)) :
    twistedSectionPushforwardEquiv f L structureModule_locallyFreeRankOne
        ((sectionNeutralTwistIso f L).inv.app ⊤ s) =
      moduleSheafDualUnitIso.hom ≫ sectionDirectImageMap f L s := by
  apply ((pullbackPushforwardAdjunction f).homEquiv _ _).symm.injective
  rw [twistedSectionPushforwardEquiv_adjoint,
    Adjunction.homEquiv_naturality_left_symm]
  rw [sectionDirectImageMap, Equiv.symm_apply_apply]
  exact neutralTwist_adjoint f L s

end FLT.Mazur.FCurve

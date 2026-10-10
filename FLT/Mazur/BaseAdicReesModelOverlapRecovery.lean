/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelProjectionCompatibility
public import FLT.Mazur.ModuleSheafChartOverlapRecovery
public import FLT.Mazur.ModuleSheafChartRecoveryRefinement

/-!
# Recovery of the descended model on its original overlaps

The descended projections satisfy the original full-overlap comparison.
Fixed coordinate isomorphisms retain the original coefficient transition,
and recover the first projection without selecting new identifications.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

attribute [local instance] spectrumSpaceMap_isOpenImmersion
attribute [local irreducible] Scheme.Modules.pullback spectrumSheaf
attribute [local irreducible] spectrumImageSheaf spectrumChartImageTransition

attribute [local irreducible] spectrumSpaceMap spectrumOverlapSheafIso

open SheafPullbackPathComparison ModuleSheafOverlapImageTransition
open ModuleSheafMorphismGluing ModuleSheafOpenImmersionLocalHom

/-- Recovery of an original chart by genuine module pullback. -/
@[irreducible]
def spectrumModelChartRecovery (U : X.affineOpens) :
    (pullback (spectrumSpaceMap f J U)).obj (spectrumDescendedSheaf f J M) ≅
      spectrumSheaf f J M U :=
  (restrictFunctorIsoPullback (spectrumSpaceMap f J U)).symm.app
      (spectrumDescendedSheaf f J M) ≪≫ spectrumDescendedSheafChartIso f J M U

/-- Pullback chart recovery is induced by the actual descended projection. -/
lemma spectrumModelChartRecovery_projection (U : X.affineOpens) :
    (spectrumModelChartRecovery f J M U).hom =
      (pullback (spectrumSpaceMap f J U)).map (spectrumDescendedSheafProjection f J M U) ≫
        (openCounitIso (spectrumSpaceMap f J U) (spectrumSheaf f J M U)).hom := by
  simp only [spectrumModelChartRecovery, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    spectrumDescendedSheafChartIso_projection]
  rw [← (restrictFunctorIsoPullback (spectrumSpaceMap f J U)).inv.naturality_assoc]
  rfl

/-- The global descended projections satisfy the original pulled-back overlap equation. -/
lemma spectrumDescendedSheafProjection_overlap (U V : X.affineOpens) :
    (pullback (spectrumOverlapToSpace f J U V)).map
        (spectrumDescendedSheafProjection f J M U) ≫
      (spectrumOverlapAmbientSheafIso f J M U V).hom =
        (pullback (spectrumOverlapToSpace f J U V)).map
          (spectrumDescendedSheafProjection f J M V) := by
  apply pullback_projection_of_localEval
  intro W hW s
  have hWV : W ≤ spectrumImageOpen f J U ⊓ spectrumImageOpen f J V :=
    hW.trans_eq (spectrumOverlapToSpace_opensRange f J U V)
  have h := spectrumDescendedSheafProjection_transition_app f J M U V W
    (hWV.trans inf_le_left) (hWV.trans inf_le_right) s
  have hh : localEval (spectrumAmbientChartImageTransition f J M U V).hom
      (le_inf (hWV.trans inf_le_left) (hWV.trans inf_le_right))
        ((spectrumDescendedSheafProjection f J M U).app W s) =
      (spectrumDescendedSheafProjection f J M V).app W s := by
    unfold spectrumAmbientChartImageTransition
    exact h
  rw [spectrumAmbientChartImageTransition_app f J M U V W
    (hWV.trans inf_le_left) (hWV.trans inf_le_right)] at hh
  exact hh

/-- Recover a chart after an arbitrary compatible further pullback. -/
@[irreducible]
def spectrumModelRecoveryAlong (U : X.affineOpens) {Y : Scheme.{u}}
    (a : Y ⟶ modelSpectrum f J U) (r : Y ⟶ relativeSpace f J)
    (h : a ≫ spectrumSpaceMap f J U = r) :
    (pullback r).obj (spectrumDescendedSheaf f J M) ≅
      (pullback a).obj (spectrumSheaf f J M U) :=
  (comparison a (spectrumSpaceMap f J U) r h).symm.app
      (spectrumDescendedSheaf f J M) ≪≫
    (pullback a).mapIso (spectrumModelChartRecovery f J M U)

/-- Further chart recovery is still the original global projection in overlap coordinates. -/
lemma spectrumModelRecoveryAlong_projection (U : X.affineOpens) {Y : Scheme.{u}}
    (a : Y ⟶ modelSpectrum f J U) (r : Y ⟶ relativeSpace f J)
    (h : a ≫ spectrumSpaceMap f J U = r) :
    (spectrumModelRecoveryAlong f J M U a r h).hom =
      (pullback r).map (spectrumDescendedSheafProjection f J M U) ≫
        (coordinateIso a (spectrumSpaceMap f J U) r h (spectrumSheaf f J M U)).hom := by
  unfold spectrumModelRecoveryAlong
  exact coordinateIso_projection _ _ _ (spectrumModelChartRecovery_projection f J M U) a r h

/-- The first original overlap coordinate, with its ambient module type fixed. -/
@[irreducible]
def spectrumModelFirstCoordinate (U V : X.affineOpens) :
    (pullback (spectrumOverlapToSpace f J U V)).obj (spectrumAmbientSheaf f J M U) ≅
      (pullback (spectrumOverlapFirst f J U V)).obj (spectrumSheaf f J M U) :=
  coordinateIso (spectrumOverlapFirst f J U V) (spectrumSpaceMap f J U)
    (spectrumOverlapToSpace f J U V) rfl (spectrumSheaf f J M U)

/-- The second original overlap coordinate, with its ambient module type fixed. -/
@[irreducible]
def spectrumModelSecondCoordinate (U V : X.affineOpens) :
    (pullback (spectrumOverlapToSpace f J U V)).obj (spectrumAmbientSheaf f J M V) ≅
      (pullback (spectrumOverlapSecond f J U V)).obj (spectrumSheaf f J M V) :=
  coordinateIso (spectrumOverlapSecond f J U V) (spectrumSpaceMap f J V)
    (spectrumOverlapToSpace f J U V) (spectrumOverlap_condition f J U V).symm
    (spectrumSheaf f J M V)

/-- The ambient map is the original coefficient comparison in these fixed coordinates. -/
lemma spectrumModelOverlapIso_eq (U V : X.affineOpens) :
    spectrumOverlapAmbientSheafIso f J M U V =
      spectrumModelFirstCoordinate f J M U V ≪≫ spectrumOverlapSheafIso f J M U V ≪≫
        (spectrumModelSecondCoordinate f J M U V).symm := by
  unfold spectrumModelFirstCoordinate spectrumModelSecondCoordinate
  rfl

/-- The ambient overlap map retains its original coefficient coordinate equation. -/
lemma spectrumModelOverlapCoordinate (U V : X.affineOpens) :
    (spectrumOverlapAmbientSheafIso f J M U V).hom ≫
      (spectrumModelSecondCoordinate f J M U V).hom =
      (spectrumModelFirstCoordinate f J M U V).hom ≫
        (spectrumOverlapSheafIso f J M U V).hom := by
  rw [spectrumModelOverlapIso_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- Recovery through the first overlap coordinate is the first actual projection. -/
lemma spectrumModelRecoveryAlong_first (U V : X.affineOpens) :
    (spectrumModelRecoveryAlong f J M U (spectrumOverlapFirst f J U V)
      (spectrumOverlapToSpace f J U V) rfl).hom =
        (pullback (spectrumOverlapToSpace f J U V)).map
          (spectrumDescendedSheafProjection f J M U) ≫
          (spectrumModelFirstCoordinate f J M U V).hom := by
  unfold spectrumModelFirstCoordinate
  exact spectrumModelRecoveryAlong_projection f J M U _ _ _

end FLT.Mazur.BaseAdicRees

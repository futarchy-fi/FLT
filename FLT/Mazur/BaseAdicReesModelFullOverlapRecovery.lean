/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelOverlapRecovery

/-!
# Recovery of the descended model on its original overlaps

The chart recovery maps satisfy the original full-overlap comparison, as
maps of actual pullback sheaves. This retains the canonical descent maps
and the original coefficient transition, without selecting new identifications.
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

/-- The second coordinate is normalized by the original overlap condition. -/
lemma spectrumModelSecondCoordinate_eq (U V : X.affineOpens) :
    spectrumModelSecondCoordinate f J M U V =
      coordinateIso (spectrumOverlapSecond f J U V) (spectrumSpaceMap f J V)
        (spectrumOverlapToSpace f J U V) (spectrumOverlap_condition f J U V).symm
        (spectrumSheaf f J M V) := by
  unfold spectrumModelSecondCoordinate
  rfl

/-- Recovery through the second overlap coordinate is the second actual projection. -/
lemma spectrumModelRecoveryAlong_second (U V : X.affineOpens) :
    (spectrumModelRecoveryAlong f J M V (spectrumOverlapSecond f J U V)
      (spectrumOverlapToSpace f J U V) (spectrumOverlap_condition f J U V).symm).hom =
        (pullback (spectrumOverlapToSpace f J U V)).map
          (spectrumDescendedSheafProjection f J M V) ≫
          (spectrumModelSecondCoordinate f J M U V).hom := by
  rw [spectrumModelSecondCoordinate_eq]
  exact spectrumModelRecoveryAlong_projection f J M V
    (spectrumOverlapSecond f J U V) (spectrumOverlapToSpace f J U V)
    (spectrumOverlap_condition f J U V).symm

/-- The recovered original chart sheaves obey their actual full-overlap transition. -/
lemma spectrumModelRecoveryAlong_overlap (U V : X.affineOpens) :
    (spectrumModelRecoveryAlong f J M U (spectrumOverlapFirst f J U V)
        (spectrumOverlapToSpace f J U V) rfl).hom ≫
      (spectrumOverlapSheafIso f J M U V).hom =
        (spectrumModelRecoveryAlong f J M V (spectrumOverlapSecond f J U V)
          (spectrumOverlapToSpace f J U V) (spectrumOverlap_condition f J U V).symm).hom := by
  exact ModuleSheafChartRecoveryRefinement.recovery_of_projection _ _ _ _ _ _ _ _
    (spectrumModelRecoveryAlong_first f J M U V)
    (spectrumModelRecoveryAlong_second f J M U V)
    (spectrumModelOverlapCoordinate f J M U V)
    (spectrumDescendedSheafProjection_overlap f J M U V)

end FLT.Mazur.BaseAdicRees

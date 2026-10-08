/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelAffineRecovery
public import FLT.Mazur.BaseAdicReesSpectrumIdentity

/-!
# Recovery of original nested affine restrictions

The descended chart recovery commutes with the original model restriction.
The identity normalization removes the auxiliary self-pullback coordinate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.BaseAdicRees

open SheafPullbackPathComparison

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

attribute [local irreducible] Scheme.Modules.pullback spectrumSheaf spectrumSpaceMap

/-- Normalization of the original self-chart recovers the chosen chart isomorphism. -/
lemma spectrumModelAffineRecovery_self (U : X.affineOpens) :
    (spectrumModelAffineRecovery f J M (U := U) le_rfl).hom ≫
        spectrumRestriction f J M le_rfl = (spectrumModelChartRecovery f J M U).hom := by
  rw [spectrumRestriction_self]
  unfold spectrumModelAffineRecovery spectrumModelRecoveryAlong
  exact ModuleSheafIdentityRecovery.recovery_self (spectrumSpaceMap f J U)
    (spectrumMap f J le_rfl) (spectrumMap_self f J U) (spectrumMap_chart f J le_rfl)
    (spectrumDescendedSheaf f J M) (spectrumSheaf f J M U)
    (spectrumModelChartRecovery f J M U).hom

/-- Nested affine recovery followed by the original restriction is the smaller chart recovery. -/
lemma spectrumModelAffineRecovery_restriction {U V : X.affineOpens} (h : U.1 ≤ V.1) :
    (spectrumModelAffineRecovery f J M h).hom ≫ spectrumRestriction f J M h =
      (spectrumModelChartRecovery f J M U).hom := by
  rw [← spectrumAffineOverlap_restriction f J M h le_rfl, ← Category.assoc,
    spectrumModelAffineRecovery_overlap, spectrumModelAffineRecovery_self]

/-- The chosen chart recoveries commute with the original pullback restriction morphisms. -/
lemma spectrumModelChartRecovery_naturality {U V : X.affineOpens} (h : U.1 ≤ V.1) :
    (pullback (spectrumMap f J h)).map (spectrumModelChartRecovery f J M V).hom ≫
        spectrumRestriction f J M h =
      (comparison (spectrumMap f J h) (spectrumSpaceMap f J V)
        (spectrumSpaceMap f J U) (spectrumMap_chart f J h)).hom.app
          (spectrumDescendedSheaf f J M) ≫ (spectrumModelChartRecovery f J M U).hom := by
  apply (cancel_epi ((comparison (spectrumMap f J h) (spectrumSpaceMap f J V)
    (spectrumSpaceMap f J U) (spectrumMap_chart f J h)).inv.app
      (spectrumDescendedSheaf f J M))).mp
  rw [Iso.inv_hom_id_app_assoc]
  have hh := spectrumModelAffineRecovery_restriction f J M h
  unfold spectrumModelAffineRecovery spectrumModelRecoveryAlong at hh
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    Category.assoc] using hh

end FLT.Mazur.BaseAdicRees

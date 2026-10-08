/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumRestriction
public import FLT.Mazur.ModuleSheafIdentityCocycle

/-!
# Identity normalization for the original Rees restriction

The original invertible restriction cocycle forces its self-transition to
be the canonical identity pullback comparison.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

attribute [local irreducible] Scheme.Modules.pullback spectrumSheaf spectrumMap
attribute [local irreducible] spectrumCompositeIso

/-- A self-transition is the canonical identity pullback comparison. -/
lemma spectrumRestriction_self (U : X.affineOpens) :
    spectrumRestriction f J M (U := U) le_rfl =
      (pullbackCongr (spectrumMap_self f J U)).hom.app (spectrumSheaf f J M U) ≫
        (pullbackId (modelSpectrum f J U)).hom.app (spectrumSheaf f J M U) :=
  ModuleSheafIdentityCocycle.self_eq_unit (X := modelSpectrum f J U)
    (spectrumMap f J le_rfl) (spectrumMap_self f J U)
    (spectrumMap_comp f J le_rfl le_rfl) (spectrumSheaf f J M U)
    (spectrumRestriction f J M le_rfl) (spectrumCompositeIso f J M le_rfl le_rfl)
    (spectrumCompositeIso_path f J M le_rfl le_rfl)
    (spectrumRestriction_comp f J M le_rfl le_rfl)

end FLT.Mazur.BaseAdicRees

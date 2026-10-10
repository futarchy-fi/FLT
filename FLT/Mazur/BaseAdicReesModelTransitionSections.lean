/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesNativeSectionNaturality

/-!
# Original section formulas for the model transition

The actual sheaf transition, evaluated after the pullback unit, is the
original coefficient restriction. Consequently its recovered power sections
restrict degree by degree by the original ideal-power sheaves.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.BaseAdicThickening
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]


/-- Recovering coefficients inverts the canonical map to global tilde sections. -/
lemma modelSheafTopCoefficientsEquiv_symm (V : X.affineOpens)
    (s : nativeModule f J M V) :
    let _ := chartAlgebra f V
    (modelSheafTopCoefficientsEquiv f J M V).symm s =
      tilde.toOpen (R := .of (Γ(X, V.1) ⊗[R] reesAlgebra J))
        (nativeModule f J M V) ⊤ s := by
  let _ := chartAlgebra f V
  rfl

/-- The original model restriction acts on global sections through its adjunction unit. -/
def modelTransitionSections {U V : X.affineOpens} (h : U.1 ≤ V.1) :
    Γ(modelSheaf f J V M, ⊤) →+ Γ(modelSheaf f J U M, ⊤) :=
  ((modelRestriction f J M h).app ⊤).hom.comp
    ((((pullbackPushforwardAdjunction (modelMap f J h)).unit.app
      (modelSheaf f J V M)).app ⊤).hom)

/-- On native coefficients, the actual sheaf transition is the original restriction. -/
lemma modelTransitionSections_native {U V : X.affineOpens} (h : U.1 ≤ V.1)
    (s : nativeModule f J M V) :
    modelTransitionSections f J M h ((modelSheafTopCoefficientsEquiv f J M V).symm s) =
      (modelSheafTopCoefficientsEquiv f J M U).symm (nativeRestriction f J M h s) := by
  let _ := chartAlgebra f U
  let _ := chartAlgebra f V
  rw [modelSheafTopCoefficientsEquiv_symm, modelSheafTopCoefficientsEquiv_symm]
  unfold modelTransitionSections modelRestriction
  exact AffineTildeSemilinearMap.map_unit
    (CommRingCat.ofHom (relativeRingRestriction f J h).toRingHom)
    (nativeModule f J M V) (nativeModule f J M U) (nativeRestriction f J M h) s

/-- Every model section restricts by the original coefficient map. -/
lemma modelTransitionSections_coefficients {U V : X.affineOpens} (h : U.1 ≤ V.1)
    (s : Γ(modelSheaf f J V M, ⊤)) :
    modelSheafTopCoefficientsEquiv f J M U (modelTransitionSections f J M h s) =
      nativeRestriction f J M h (modelSheafTopCoefficientsEquiv f J M V s) := by
  obtain ⟨t, rfl⟩ := (modelSheafTopCoefficientsEquiv f J M V).symm.surjective s
  rw [modelTransitionSections_native, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- The original sheaf transition recovers the original direct sum of power restrictions. -/
lemma modelTransitionSections_powerSections {U V : X.affineOpens} (h : U.1 ≤ V.1)
    (s : Γ(modelSheaf f J V M, ⊤)) :
    nativePowerSectionsEquiv f J M U
        (modelSheafTopCoefficientsEquiv f J M U (modelTransitionSections f J M h s)) =
      IdealPowerRees.chartRestriction ((baseIdeal R J).comap f) M V h le_rfl
        (homOfLE h) (nativePowerSectionsEquiv f J M V
          (modelSheafTopCoefficientsEquiv f J M V s)) := by
  rw [modelTransitionSections_coefficients, nativePowerSectionsEquiv_restriction]

end FLT.Mazur.BaseAdicRees

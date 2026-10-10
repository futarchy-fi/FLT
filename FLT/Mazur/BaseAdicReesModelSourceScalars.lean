/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSourceScalars
public import FLT.Mazur.BaseAdicReesModelCoefficientScalars
public import FLT.Mazur.BaseAdicReesNativeSectionNaturality
public import FLT.Mazur.ModuleSheafProjectionScalars

/-!
# Source linearity of the actual pushforward power coordinates

The chosen section identification retains the original action of the source
chart ring, through the actual projection and the original tensor inclusion.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

attribute [local semireducible] modelSpectrum
attribute [local irreducible] modelSheaf chartSpaceMap spectrumDescendedSheaf
attribute [local irreducible] spectrumDescendedSheafProjection

/-- Source scalars act on the original chart sections by the original tensor inclusion. -/
lemma modelPushforwardChartSectionsIso_smul (V : X.affineOpens)
    (a : Γ(X, V.1)) (s : Γ(modelPushforward f J M, V.1)) :
    let _ := chartAlgebra f V
    (modelPushforwardChartSectionsIso f J M V).hom (a • s) =
      (Scheme.ΓSpecIso (.of (Γ(X, V.1) ⊗[R] reesAlgebra J))).inv
          (algebraMap Γ(X, V.1) (Γ(X, V.1) ⊗[R] reesAlgebra J) a) •
        (modelPushforwardChartSectionsIso f J M V).hom s := by
  let _ := chartAlgebra f V
  rw [modelPushforwardChartSectionsIso_projection]
  have hh := ModuleSheafProjectionSections.sections_pushforward_smul
    (spectrumSpaceMap f J V) (spectrumDescendedSheaf f J M) (spectrumSheaf f J M V)
    (spectrumDescendedSheafProjection f J M V) (modelSourceProjection f J)
    V.1 ⊤ (spectrumSpaceMap_preimage_source f J V) a s
  rw [spectrumSourceProjection_appLE] at hh
  exact hh

/-- The actual recovered power sections are linear over the original source chart ring. -/
lemma modelPushforwardPowerSectionsIso_smul (V : X.affineOpens)
    (a : Γ(X, V.1)) (s : Γ(modelPushforward f J M, V.1)) :
    (modelPushforwardPowerSectionsIso f J M V).hom (a • s) =
      a • (modelPushforwardPowerSectionsIso f J M V).hom s := by
  let _ := chartAlgebra f V
  let _ := Rees.relativeModule (S := Γ(X, V.1)) (M := Γ(M, V.1)) J
  change nativePowerSectionsEquiv f J M V
      (modelSheafTopCoefficientsEquiv f J M V
        ((modelPushforwardChartSectionsIso f J M V).hom (a • s))) = _
  rw [modelPushforwardChartSectionsIso_smul, modelSheafTopCoefficientsEquiv_smul]
  change nativePowerSectionsEquiv f J M V
      ((algebraMap Γ(X, V.1) (Γ(X, V.1) ⊗[R] reesAlgebra J) a) •
        (show Rees.extendedModule (S := Γ(X, V.1)) (M := Γ(M, V.1)) J from
          modelSheafTopCoefficientsEquiv f J M V
            ((modelPushforwardChartSectionsIso f J M V).hom s))) = _
  rw [Rees.relativeModule_algebraMap_smul, nativePowerSectionsEquiv_smul]
  rfl

end FLT.Mazur.BaseAdicRees

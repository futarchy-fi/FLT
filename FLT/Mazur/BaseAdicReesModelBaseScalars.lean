/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesBaseScalars
public import FLT.Mazur.BaseAdicReesNativeBaseScalars
public import FLT.Mazur.BaseAdicReesModelCoefficientScalars
public import FLT.Mazur.ModuleSheafProjectionScalars

/-!
# Base Rees linearity of the actual pushforward power coordinates

The original structural base Rees scalar on the actual direct image corresponds
to the original coefficientwise action on all original ideal-power sections.
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

attribute [local semireducible] modelSpectrum
attribute [local irreducible] modelSheaf chartSpaceMap spectrumDescendedSheaf
attribute [local irreducible] spectrumDescendedSheafProjection

/-- The original base scalar on the direct image acts by its right tensor coordinate. -/
lemma modelPushforwardChartSectionsIso_base_smul (V : X.affineOpens)
    (a : reesAlgebra J) (s : Γ(modelPushforward f J M, V.1)) :
    let _ := chartAlgebra f V
    (modelPushforwardChartSectionsIso f J M V).hom
        (modelBaseScalar f J V a •
          (show Γ(globalModelSheaf f J M, modelSourceProjection f J ⁻¹ᵁ V.1) from s)) =
      (Scheme.ΓSpecIso (.of (Γ(X, V.1) ⊗[R] reesAlgebra J))).inv
          (Algebra.TensorProduct.includeRight (R := R) (A := Γ(X, V.1)) a) •
        (modelPushforwardChartSectionsIso f J M V).hom s := by
  let _ := chartAlgebra f V
  rw [modelPushforwardChartSectionsIso_projection]
  have hh := ModuleSheafProjectionSections.sections_smul
    (spectrumSpaceMap f J V) (spectrumDescendedSheaf f J M) (spectrumSheaf f J M V)
    (spectrumDescendedSheafProjection f J M V) (modelSourceProjection f J ⁻¹ᵁ V.1) ⊤
    (spectrumSpaceMap_preimage_source f J V) (modelBaseScalar f J V a) s
  rw [spectrumBaseProjection_appLE] at hh
  exact hh

/-- Actual pushforward power coordinates preserve the original coefficientwise Rees action. -/
lemma modelPushforwardPowerSectionsIso_base_smul (V : X.affineOpens)
    (a : reesAlgebra J) (s : Γ(modelPushforward f J M, V.1)) :
    let _ := IdealPowerRees.sectionsModule ((baseIdeal R J).comap f) M V
    (modelPushforwardPowerSectionsIso f J M V).hom
        (modelBaseScalar f J V a •
          (show Γ(globalModelSheaf f J M, modelSourceProjection f J ⁻¹ᵁ V.1) from s)) =
      chartReesScalars f J V a • (modelPushforwardPowerSectionsIso f J M V).hom s := by
  let _ := chartAlgebra f V
  let _ := IdealPowerRees.sectionsModule ((baseIdeal R J).comap f) M V
  change nativePowerSectionsEquiv f J M V
      (modelSheafTopCoefficientsEquiv f J M V
        ((modelPushforwardChartSectionsIso f J M V).hom _)) = _
  rw [modelPushforwardChartSectionsIso_base_smul, modelSheafTopCoefficientsEquiv_smul,
    nativePowerSectionsEquiv_base_smul]
  rfl

end FLT.Mazur.BaseAdicRees

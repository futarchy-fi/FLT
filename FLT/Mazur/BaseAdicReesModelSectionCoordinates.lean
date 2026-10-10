/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelPushforward

/-!
# Original power sections in the affine direct image of the Rees model

The actual pushforward on each original affine open is the full direct sum
of sections of the original ideal powers. These coordinates use the already
descended model and the original chart sheaves and inclusions.
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
  (V : X.affineOpens)

/-- The original chart sheaf is the tilde of its actual native coefficient module. -/
lemma modelSheaf_eq_tilde_native :
    modelSheaf f J V M = tilde (nativeModule f J M V) := rfl

attribute [local irreducible] modelSheaf

/-- Global sections of the original chart sheaf recover its actual coefficients. -/
def modelSheafTopCoefficientsEquiv : Γ(modelSheaf f J V M, ⊤) ≃+ nativeModule f J M V := by
  let _ := chartAlgebra f V
  rw [modelSheaf_eq_tilde_native]
  exact ((tilde.toTildeΓNatIso (R := .of (Γ(X, V.1) ⊗[R] reesAlgebra J))).app
    (nativeModule f J M V)).symm.toLinearEquiv.toAddEquiv

/-- Native coefficients retain the original direct-sum section coordinates. -/
@[irreducible]
def nativePowerSectionsEquiv : nativeModule f J M V ≃+
    IdealPowerRees.Sections ((baseIdeal R J).comap f) M V := by
  let _ := chartAlgebra f V
  exact (sectionsEquiv f J V M).symm.toAddEquiv

/-- Native section coordinates invert the original polynomial coefficient comparison. -/
lemma nativePowerSectionsEquiv_coordinates (s : nativeModule f J M V) :
    let _ := chartAlgebra f V
    sectionsEquiv f J V M (nativePowerSectionsEquiv f J M V s) = s := by
  let _ := chartAlgebra f V
  unfold nativePowerSectionsEquiv
  exact (sectionsEquiv f J V M).apply_symm_apply s

/-- The affine direct image consists of all original power sections, in their original degrees. -/
def modelPushforwardPowerSectionsIso :
    Γ(modelPushforward f J M, V.1) ≅
      AddCommGrpCat.of (IdealPowerRees.Sections ((baseIdeal R J).comap f) M V) := by
  let e₁ : Γ(modelSheaf f J V M, ⊤) ≅ AddCommGrpCat.of (nativeModule f J M V) :=
    (modelSheafTopCoefficientsEquiv f J M V).toAddCommGrpIso
  let e₂ : AddCommGrpCat.of (nativeModule f J M V) ≅
      AddCommGrpCat.of (IdealPowerRees.Sections ((baseIdeal R J).comap f) M V) :=
    (nativePowerSectionsEquiv f J M V).toAddCommGrpIso
  exact modelPushforwardChartSectionsIso f J M V ≪≫ e₁ ≪≫ e₂

/-- The recovered direct sum has exactly the coefficients of the original model section. -/
lemma modelPushforwardPowerSectionsIso_coordinates (s : Γ(modelPushforward f J M, V.1)) :
    let _ := chartAlgebra f V
    sectionsEquiv f J V M ((modelPushforwardPowerSectionsIso f J M V).hom s) =
      modelSheafTopCoefficientsEquiv f J M V
        ((modelPushforwardChartSectionsIso f J M V).hom s) := by
  let _ := chartAlgebra f V
  exact nativePowerSectionsEquiv_coordinates f J M V _

/-- Each native model coefficient is the original ideal-power inclusion of the recovered section. -/
lemma modelPushforwardPowerSectionsIso_coeff
    (s : Γ(modelPushforward f J M, V.1)) (n : ℕ) :
    let _ := chartAlgebra f V
    (show Rees.extendedModule (S := Γ(X, V.1)) (M := Γ(M, V.1)) J from
      modelSheafTopCoefficientsEquiv f J M V
        ((modelPushforwardChartSectionsIso f J M V).hom s)).val.coeff n =
      (GlobalIdealPower.inclusion (((baseIdeal R J).comap f) ^ n) M).app V.1
        ((modelPushforwardPowerSectionsIso f J M V).hom s n) := by
  let _ := chartAlgebra f V
  rw [← modelPushforwardPowerSectionsIso_coordinates]
  exact sectionsEquiv_coeff f J V M _ n

end FLT.Mazur.BaseAdicRees

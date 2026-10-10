/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesNativeSectionNaturality
public import FLT.Mazur.IdealPowerReesAction

/-!
# Original base Rees action on power-section coordinates

The base Rees ring acts on original power sections through its coefficientwise
map into the original chart Rees ring. Native coordinates retain this action.
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

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (J : Ideal R)

/-- Coefficientwise base change into the original chart ideal's Rees algebra. -/
def chartReesScalars (V : X.affineOpens) :
    reesAlgebra J →+* reesAlgebra (((baseIdeal R J).comap f).ideal V) :=
  Rees.algebraMap J _ (chartScalars f V) (by
    let _ := chartAlgebra f V
    rw [chartIdeal_eq]
    exact le_rfl)

variable [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

/-- The original power-section comparison retains the coefficientwise base Rees action. -/
lemma sectionsEquiv_base_smul (V : X.affineOpens) (a : reesAlgebra J)
    (s : IdealPowerRees.Sections ((baseIdeal R J).comap f) M V) :
    let _ := chartAlgebra f V
    let _ := IdealPowerRees.sectionsModule ((baseIdeal R J).comap f) M V
    let _ := Rees.relativeModule (S := Γ(X, V.1)) (M := Γ(M, V.1)) J
    sectionsEquiv f J V M (chartReesScalars f J V a • s) =
      Algebra.TensorProduct.includeRight (R := R) (A := Γ(X, V.1)) a •
        sectionsEquiv f J V M s := by
  let _ := chartAlgebra f V
  let _ := IdealPowerRees.sectionsModule ((baseIdeal R J).comap f) M V
  let _ := Rees.relativeModule (S := Γ(X, V.1)) (M := Γ(M, V.1)) J
  apply Subtype.ext
  change (affineModuleEquiv f J V M
    (IdealPowerRees.sectionsEquiv _ M V (chartReesScalars f J V a • s))).val = _
  rw [affineModuleEquiv_val, IdealPowerRees.sectionsModule_smul]
  change (chartReesScalars f J V a).val • (IdealPowerRees.sectionsEquiv _ M V s).val =
    (Rees.relativeMap J ((1 : Γ(X, V.1)) ⊗ₜ[R] a)).val • (sectionsEquiv f J V M s).val
  rw [Rees.relativeMap_tmul, one_smul]
  change _ = (Rees.baseChangeMap J a).val •
    (affineModuleEquiv f J V M (IdealPowerRees.sectionsEquiv _ M V s)).val
  rw [affineModuleEquiv_val]
  rfl

/-- Native coefficients recover the original base Rees action on power sections. -/
lemma nativePowerSectionsEquiv_base_smul (V : X.affineOpens) (a : reesAlgebra J)
    (s : nativeModule f J M V) :
    let _ := chartAlgebra f V
    let _ := IdealPowerRees.sectionsModule ((baseIdeal R J).comap f) M V
    nativePowerSectionsEquiv f J M V
        (Algebra.TensorProduct.includeRight (R := R) (A := Γ(X, V.1)) a • s) =
      chartReesScalars f J V a • nativePowerSectionsEquiv f J M V s := by
  let _ := chartAlgebra f V
  let _ := IdealPowerRees.sectionsModule ((baseIdeal R J).comap f) M V
  let _ := Rees.relativeModule (S := Γ(X, V.1)) (M := Γ(M, V.1)) J
  apply (sectionsEquiv f J V M).injective
  rw [nativePowerSectionsEquiv_coordinates, sectionsEquiv_base_smul,
    nativePowerSectionsEquiv_coordinates]

end FLT.Mazur.BaseAdicRees

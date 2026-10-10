/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesTensorModule
public import FLT.Mazur.BaseAdicReesLocalization

/-!
# Localization over the actual relative Rees tensor rings

The original principal restriction of the whole relative power module is a
localization over the larger tensor ring. Both its map and denominator are
the ones identified by the actual relative chart geometry.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec R) (J : Ideal R) (M : X.Modules) [M.IsFinitePresentation]
  (V : X.affineOpens)

/-- The actual whole-power restriction localizes over the relative tensor ring. -/
theorem chartTensorRestriction_isLocalized (r : Γ(X, V.1)) :
    let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
    let _ := chartAlgebra f V
    let _ := chartTensorModule f J M V V le_rfl
    let _ := chartTensorModule f J M V U (X.basicOpen_le r)
    IsLocalizedModule.Away (algebraMap Γ(X, V.1)
      (Γ(X, V.1) ⊗[R] reesAlgebra J) r)
      (chartTensorRestriction f J M V (U := U) (X.basicOpen_le r) le_rfl
        (X.basicOpen_le r)) := by
  let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
  let _ := chartAlgebra f V
  let _ := chartTensorModule f J M V V le_rfl
  let _ := chartTensorModule f J M V U (X.basicOpen_le r)
  let _ := chartTensorModule_scalarTower f J M V V le_rfl
  let _ := chartTensorModule_scalarTower f J M V U (X.basicOpen_le r)
  let g := chartTensorRestriction f J M V (U := U) (X.basicOpen_le r) le_rfl
    (X.basicOpen_le r)
  have he : g.restrictScalars Γ(X, V.1) =
      chartModuleRestriction f J M V (U := U) (X.basicOpen_le r) le_rfl
        (X.basicOpen_le r) := rfl
  have : IsLocalizedModule.Away r (g.restrictScalars Γ(X, V.1)) := by
    rw [he]
    exact chartModuleRestriction_isLocalized f J M V r
  have ht := IsLocalizedModule.of_restrictScalars (Submonoid.powers r) g
  rw [Algebra.algebraMapSubmonoid_powers] at ht
  exact ht

/-- Principal restriction is scalar extension along the actual relative tensor-ring map. -/
theorem chartTensorRestriction_isBaseChange (r : Γ(X, V.1)) :
    let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
    let _ := chartAlgebra f V
    let _ := chartAlgebra f U
    let _ : Module (Γ(X, U.1) ⊗[R] reesAlgebra J)
        (chartModule f J M V U (X.basicOpen_le r)) :=
      Rees.relativeModule (S := Γ(X, U.1)) (M := Γ(M, U.1)) J
    let _ := chartTensorModule f J M V V le_rfl
    let _ := chartTensorModule f J M V U (X.basicOpen_le r)
    let _ := Rees.relativeMapAlgebra J
      (chartRingRestriction f (U := U) (V := V) (X.basicOpen_le r))
    let _ : IsScalarTower (Γ(X, V.1) ⊗[R] reesAlgebra J)
        (Γ(X, U.1) ⊗[R] reesAlgebra J) (chartModule f J M V U (X.basicOpen_le r)) :=
      ⟨fun a b m ↦ mul_smul (relativeRingRestriction f J (U := U) (V := V)
        (X.basicOpen_le r) a) b m⟩
    IsBaseChange (Γ(X, U.1) ⊗[R] reesAlgebra J)
      (chartTensorRestriction f J M V (U := U) (X.basicOpen_le r) le_rfl
        (X.basicOpen_le r)) := by
  let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
  let _ := chartAlgebra f V
  let _ := chartAlgebra f U
  let _ : Module (Γ(X, U.1) ⊗[R] reesAlgebra J)
      (chartModule f J M V U (X.basicOpen_le r)) :=
    Rees.relativeModule (S := Γ(X, U.1)) (M := Γ(M, U.1)) J
  let _ := chartTensorModule f J M V V le_rfl
  let _ := chartTensorModule f J M V U (X.basicOpen_le r)
  let _ := Rees.relativeMapAlgebra J
    (chartRingRestriction f (U := U) (V := V) (X.basicOpen_le r))
  let _ : IsScalarTower (Γ(X, V.1) ⊗[R] reesAlgebra J)
      (Γ(X, U.1) ⊗[R] reesAlgebra J) (chartModule f J M V U (X.basicOpen_le r)) :=
    ⟨fun a b m ↦ mul_smul (relativeRingRestriction f J (U := U) (V := V)
      (X.basicOpen_le r) a) b m⟩
  let _ := relativeRingRestriction_isLocalization f J V r
  let _ := chartTensorRestriction_isLocalized f J M V r
  exact IsLocalizedModule.isBaseChange
    (Submonoid.powers (algebraMap Γ(X, V.1) (Γ(X, V.1) ⊗[R] reesAlgebra J) r))
    (Γ(X, U.1) ⊗[R] reesAlgebra J) _

end FLT.Mazur.BaseAdicRees

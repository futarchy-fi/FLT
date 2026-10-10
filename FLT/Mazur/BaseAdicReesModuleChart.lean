/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesRestriction

/-!
# Original chart-linear localization of the relative models

The actual extended-ideal polynomial modules retain their coefficient-ring
localization. Their coordinates preserve the original restriction maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.BaseAdicThickening

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) (M : X.Modules) (V : X.affineOpens)

/-- Relative polynomial modules with scalars from a fixed ambient source chart. -/
abbrev chartModule (U : X.affineOpens) (h : U.1 ≤ V.1) : ModuleCat Γ(X, V.1) :=
  let _ := chartAlgebra f U
  (ModuleCat.restrictScalars (X.presheaf.map (homOfLE h).op).hom).obj
    (ModuleCat.of Γ(X, U.1)
      (Rees.extendedModule (S := Γ(X, U.1)) (M := Γ(M, U.1)) J))

/-- Actual relative restriction, linear over the original ambient chart. -/
def chartModuleRestriction {U W : X.affineOpens}
    (hU : U.1 ≤ V.1) (hW : W.1 ≤ V.1) (h : U.1 ≤ W.1) :
    chartModule f J M V W hW →ₗ[Γ(X, V.1)] chartModule f J M V U hU where
  toFun := relativeRestriction f J M h
  map_add' := map_add _
  map_smul' r s := by
    apply Subtype.ext
    ext n
    change M.presheaf.map (homOfLE h).op
        (X.presheaf.map (homOfLE hW).op r • s.val.coeff n) =
      X.presheaf.map (homOfLE hU).op r • _
    rw [M.map_smul, ← Functor.map_comp_apply]
    rfl

variable [IsLocallyNoetherian X] [M.IsFinitePresentation]

/-- The ideal comparison also preserves scalars from a fixed larger chart. -/
def chartModuleEquiv (U : X.affineOpens) (h : U.1 ≤ V.1) :
    IdealPowerRees.chartModule ((baseIdeal R J).comap f) M V U h ≃ₗ[Γ(X, V.1)]
      chartModule f J M V U h :=
  { (affineModuleEquiv f J U M).toAddEquiv with
    map_smul' r s := (affineModuleEquiv f J U M).map_smul
      (X.presheaf.map (homOfLE h).op r) s }

omit [IsLocallyNoetherian X] [M.IsFinitePresentation] in
/-- These relative coordinates commute with the original polynomial restriction. -/
lemma chartModuleEquiv_restriction {U W : X.affineOpens}
    (hU : U.1 ≤ V.1) (hW : W.1 ≤ V.1) (h : U.1 ≤ W.1)
    (s : IdealPowerRees.chartModule ((baseIdeal R J).comap f) M V W hW) :
    chartModuleEquiv f J M V U hU
      (IdealPowerRees.chartModuleRestriction _ M V hU hW h s) =
      chartModuleRestriction f J M V hU hW h (chartModuleEquiv f J M V W hW s) := by
  apply Subtype.ext
  ext n
  change (affineModuleEquiv f J U M _).val.coeff n =
    (relativeRestriction f J M h (affineModuleEquiv f J W M s)).val.coeff n
  rw [affineModuleEquiv_val, relativeRestriction_coeff, affineModuleEquiv_val]
  rfl

/-- The actual relative model localizes over the source chart's coordinate ring. -/
theorem chartModuleRestriction_isLocalized (r : Γ(X, V.1)) :
    IsLocalizedModule.Away r (chartModuleRestriction f J M V
      (U := ⟨X.basicOpen r, V.2.basicOpen r⟩) (X.basicOpen_le r) le_rfl
      (X.basicOpen_le r)) := by
  let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
  let e := chartModuleEquiv f J M V V le_rfl
  let e' := chartModuleEquiv f J M V U (X.basicOpen_le r)
  let a := IdealPowerRees.chartModuleRestriction ((baseIdeal R J).comap f) M V
    (U := U) (X.basicOpen_le r) le_rfl (X.basicOpen_le r)
  let b := chartModuleRestriction f J M V (U := U) (X.basicOpen_le r) le_rfl
    (X.basicOpen_le r)
  let _ := IdealPowerRees.chartModuleRestriction_isLocalized ((baseIdeal R J).comap f) M V r
  have he : e'.toLinearMap.comp a = b.comp e.toLinearMap := by
    ext s
    exact chartModuleEquiv_restriction f J M V (X.basicOpen_le r) le_rfl
      (X.basicOpen_le r) s
  have hl := IsLocalizedModule.of_linearEquiv (.powers r) a e'
  rw [he] at hl
  exact (IsLocalizedModule.comp_iff_of_bijective_right (.powers r)
    e.toLinearMap e.bijective).mp hl

end FLT.Mazur.BaseAdicRees

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealPowerReesRestriction
public import FLT.Mazur.IdealPowerReesLocalization

/-!
# Rees coordinates over a fixed affine chart

The actual section equivalences commute with restrictions. Restricting
scalars from a fixed chart makes these comparisons linear, so localization
of the full direct sum transfers to the polynomial Rees modules.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.GlobalIdealPower

universe u

namespace FLT.Mazur.IdealPowerRees

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]
  (V : X.affineOpens)

/-- Local Rees sections with scalars restricted from a fixed larger chart. -/
abbrev chartModule (U : X.affineOpens) (h : U.1 ≤ V.1) : ModuleCat Γ(X, V.1) :=
  (ModuleCat.restrictScalars (X.presheaf.map (homOfLE h).op).hom).obj
    (ModuleCat.of Γ(X, U.1) (affineModule I M U))

/-- The original affine coordinates also respect the fixed chart scalars. -/
def chartEquiv (U : X.affineOpens) (h : U.1 ≤ V.1) :
    chartSections I M V U.1 h ≃ₗ[Γ(X, V.1)] chartModule I M V U h :=
  { (sectionsEquiv I M U).toAddEquiv with
    map_smul' r s := (sectionsEquiv I M U).map_smul
      (X.presheaf.map (homOfLE h).op r) s }

/-- Actual polynomial restriction, linear over the fixed ambient chart. -/
def chartModuleRestriction {U W : X.affineOpens}
    (hU : U.1 ≤ V.1) (hW : W.1 ≤ V.1) (h : U.1 ≤ W.1) :
    chartModule I M V W hW →ₗ[Γ(X, V.1)] chartModule I M V U hU where
  toFun := moduleRestriction I M h
  map_add' := map_add _
  map_smul' r s := by
    apply Subtype.ext
    ext n
    change M.presheaf.map (homOfLE h).op
        (X.presheaf.map (homOfLE hW).op r • s.val.coeff n) =
      X.presheaf.map (homOfLE hU).op r • _
    rw [M.map_smul, ← Functor.map_comp_apply]
    rfl

/-- The coordinates intertwine restriction of the original ideal-power sheaves. -/
lemma chartEquiv_restriction {U W : X.affineOpens}
    (hU : U.1 ≤ V.1) (hW : W.1 ≤ V.1) (h : U.1 ≤ W.1)
    (s : chartSections I M V W.1 hW) :
    chartEquiv I M V U hU (chartRestriction I M V hU hW (homOfLE h) s) =
      chartModuleRestriction I M V hU hW h (chartEquiv I M V W hW s) := by
  apply Subtype.ext
  ext n
  change (sectionsEquiv I M U _).val.coeff n =
    (moduleRestriction I M h (sectionsEquiv I M W s)).val.coeff n
  rw [sectionsEquiv_coeff, moduleRestriction_coeff, sectionsEquiv_coeff]
  exact congr($((inclusion (I ^ n) M).val.naturality (homOfLE h).op) (s n))

/-- Polynomial restriction localizes the entire Rees module over the chart ring. -/
theorem chartModuleRestriction_isLocalized (r : Γ(X, V.1)) :
    IsLocalizedModule.Away r (chartModuleRestriction I M V
      (U := ⟨X.basicOpen r, V.2.basicOpen r⟩) (X.basicOpen_le r) le_rfl
      (X.basicOpen_le r)) := by
  let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
  let e := chartEquiv I M V V le_rfl
  let e' := chartEquiv I M V U (X.basicOpen_le r)
  let f := chartRestriction I M V (X.basicOpen_le r) le_rfl
    (homOfLE (X.basicOpen_le r))
  let g := chartModuleRestriction I M V (U := U) (X.basicOpen_le r) le_rfl
    (X.basicOpen_le r)
  let _ := chartRestriction_isLocalized I M V r
  have he : e'.toLinearMap.comp f = g.comp e.toLinearMap := by
    apply LinearMap.ext
    intro s
    exact chartEquiv_restriction I M V (X.basicOpen_le r) le_rfl
      (X.basicOpen_le r) s
  have hl := IsLocalizedModule.of_linearEquiv (.powers r) f e'
  rw [he] at hl
  exact (IsLocalizedModule.comp_iff_of_bijective_right (.powers r)
    e.toLinearMap e.bijective).mp hl

end FLT.Mazur.IdealPowerRees

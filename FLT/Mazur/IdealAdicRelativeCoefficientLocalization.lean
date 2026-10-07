/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicChartLocalization
public import FLT.Mazur.IdealAdicRelativeChartScalar
public import FLT.Mazur.IdealAdicRelativeLocalization

/-!
# Localization of the actual relative coefficient modules

On ambient principal refinements the original coefficient restriction is
localization over the original relative tensor ring, at its chart scalar.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.IdealAdicGradedSections

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- Coefficients on the smaller chart with the original larger relative-ring action. -/
abbrev relativeRestrictedCoefficient {U V : X.affineOpens} (i : U.1 ⟶ V.1) :
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    ModuleCat (RelativeAlgebra J f V) := by
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  exact (ModuleCat.restrictScalars (relativeRestriction J f i).toRingHom).obj
    (relativeChartCoefficient J f U)

/-- Chart coordinates on restricted coefficients retain the actual ambient scalar restriction. -/
lemma relativeChartScalar_restricted_smul {U V : X.affineOpens} (i : U.1 ⟶ V.1)
    (r : Γ(X, V.1)) (s : relativeRestrictedCoefficient J f i) :
    let := closedBaseAlgebra J f V.1
    relativeChartScalar J f V r • s =
      X.presheaf.map i.op r •
        (show IdealAdicGradedSections.Sections (J.comap f) U.1 from s) := by
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  change relativeRestriction J f i (relativeChartScalar J f V r) •
    (show relativeChartCoefficient J f U from s) = _
  rw [relativeChartScalar_restrict]
  exact relativeChartScalar_smul J f U _ _

/-- The original relative coefficient restriction localizes at the actual chart scalar. -/
lemma relativeCoefficientRestriction_isLocalized (V : X.affineOpens) (r : Γ(X, V.1)) :
    let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
    let i : U.1 ⟶ V.1 := homOfLE (X.basicOpen_le r)
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    IsLocalizedModule.Away (relativeChartScalar J f V r)
      (relativeCoefficientRestrictionLinear J f i) := by
  let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
  let i : U.1 ⟶ V.1 := homOfLE (X.basicOpen_le r)
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  let _ := chartTotalRestriction_isLocalized (J.comap f) V r
  have hsmul (a : Γ(X, V.1)) (s : relativeRestrictedCoefficient J f i) :
      relativeChartScalar J f V a • s =
        a • (show chartTotal (J.comap f) V U.1 i.le from s) :=
    relativeChartScalar_restricted_smul J f i a s
  apply IsLocalizedModule.Away.mk_of_addCommGroup
  · apply (Module.End.isUnit_iff _).mpr
    have h := (Module.End.isUnit_iff _).mp (IsLocalizedModule.Away.isUnit_algebraMap
      (chartTotalRestriction (J.comap f) V (X.basicOpen_le r) le_rfl i) r)
    change Function.Bijective (fun s : chartTotal (J.comap f) V U.1 i.le ↦ r • s) at h
    change Function.Bijective (fun s : relativeRestrictedCoefficient J f i ↦
      relativeChartScalar J f V r • s)
    rw [show (fun s : relativeRestrictedCoefficient J f i ↦
      relativeChartScalar J f V r • s) =
        (fun s : chartTotal (J.comap f) V U.1 i.le ↦ r • s) from funext (hsmul r)]
    exact h
  · intro s
    obtain ⟨n, t, ht⟩ := chartTotal_exists_numerator (J.comap f) V r s
    refine ⟨n, t, ?_⟩
    rw [← map_pow, relativeChartScalar_restricted_smul,
      map_pow, relativeCoefficientRestrictionLinear_apply]
    exact ht
  · intro s hs
    obtain ⟨n, hn⟩ := chartTotal_exists_annihilator (J.comap f) V r s hs
    refine ⟨n, ?_⟩
    rw [← map_pow, relativeChartScalar_smul]
    exact hn

end FLT.Mazur.IdealAdicGradedPullback

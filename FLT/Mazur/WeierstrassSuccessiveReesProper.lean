/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveReesProjIso
public import FLT.Mazur.BlowupReesProper

/-!
# The actual successive local contraction is proper

The global Rees comparison retains the preceding divided contraction on
both charts. Properness therefore transfers to the whole actual local step.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassSuccessiveRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] [IsDomain R]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R) (hπ : π ≠ 0)
local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "I" => WeierstrassSuccessiveX.modificationCenter W s π b3 b4 b6

/-- The horizontal chart comparison retains the actual preceding divided contraction. -/
@[reassoc] theorem horizontalChartIso_toPrevious :
    (horizontalChartIso W s π b3 b4 b6 hπ).hom ≫
        WeierstrassSuccessiveX.toDivided W s π b3 b4 b6 =
      horizontalProjInclusion W s π b3 b4 b6 ≫ BlowupRees.contraction I := by
  rw [horizontalProjInclusion, BlowupRees.fractionChartInclusion_contraction]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  apply Subtype.ext
  exact WeierstrassSuccessiveX.horizontalReesChartEquiv_fromDivided W s π b3 b4 b6 hπ a

/-- The scale chart comparison retains the actual refinement to the preceding divided chart. -/
@[reassoc] theorem scaleChartIso_toPrevious :
    (scaleChartIso W s π b3 b4 b6 (IsRegular.of_ne_zero hπ)).hom ≫
        WeierstrassSuccessiveX.dividedToPrevious W s π b3 b4 b6 =
      scaleProjInclusion W s π b3 b4 b6 ≫ BlowupRees.contraction I := by
  rw [scaleProjInclusion, BlowupRees.fractionChartInclusion_contraction]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  apply Subtype.ext
  exact WeierstrassSuccessiveScale.scaleReesChartEquiv_refinement W s π b3 b4 b6
    (IsRegular.of_ne_zero hπ) a

/-- The fraction atlas comparison retains the contraction on the whole glued scheme. -/
@[reassoc] theorem fractionAtlasIso_contraction :
    (fractionAtlasIso W s π b3 b4 b6 hπ).hom ≫
        WeierstrassSuccessiveX.contraction W s π b3 b4 b6 =
      fractionAtlasToProj W s π b3 b4 b6 hπ ≫ BlowupRees.contraction I := by
  apply pushout.hom_ext
  · change horizontalChart W s π b3 b4 b6 hπ ≫ _ =
      horizontalChart W s π b3 b4 b6 hπ ≫ _
    rw [horizontalChart_atlasIso_assoc,
      WeierstrassSuccessiveX.xChart_contraction, horizontalChartIso_toPrevious,
      horizontalChart_toProj_assoc]
  · change scaleChart W s π b3 b4 b6 hπ ≫ _ = scaleChart W s π b3 b4 b6 hπ ≫ _
    rw [scaleChart_atlasIso_assoc,
      WeierstrassSuccessiveX.dividedChart_contraction,
      scaleChartIso_toPrevious W s π b3 b4 b6 hπ,
      scaleChart_toProj_assoc]

/-- The actual whole-model comparison commutes with the original local contraction. -/
@[reassoc] theorem modificationProjIso_contraction :
    (modificationProjIso W s π b3 b4 b6 hπ).hom ≫ BlowupRees.contraction I =
      WeierstrassSuccessiveX.contraction W s π b3 b4 b6 := by
  change ((fractionAtlasIso W s π b3 b4 b6 hπ).inv ≫
    fractionAtlasToProj W s π b3 b4 b6 hπ) ≫ BlowupRees.contraction I = _
  rw [Category.assoc, ← fractionAtlasIso_contraction, Iso.inv_hom_id_assoc]

include hπ in
/-- Properness holds for the actual local two-chart replacement, including the exceptional locus. -/
theorem contraction_isProper : IsProper (WeierstrassSuccessiveX.contraction W s π b3 b4 b6) := by
  rw [← modificationProjIso_contraction W s π b3 b4 b6 hπ]
  let _ : IsProper (BlowupRees.contraction I) :=
    BlowupRees.contraction_isProper I (Submodule.fg_span (Set.toFinite _))
  infer_instance

end FLT.Mazur.WeierstrassSuccessiveRees

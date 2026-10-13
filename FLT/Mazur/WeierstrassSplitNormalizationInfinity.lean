/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitCompleteNormalization
public import FLT.Mazur.WeierstrassSlopeLaurentCubic
public import FLT.Mazur.ProjectiveLineInfinityTorusGluing

/-!
# The complete split normalization retains the full infinity chart

Glue the original affine normalization to the actual Laurent infinity chart.
Uniqueness of the proper extension identifies this explicit gluing with the
complete normalization already used by the residue exterior.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur
open ProjectiveLine WeierstrassIntegralChart WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {K : Type u} [Field K] (a : Kˣ)
local notation "W" => splitNodalEquation a
local notation "N" => splitCompleteNormalization W rfl rfl rfl rfl
local notation "F" => splitAffineToCubic W rfl rfl rfl rfl
local notation "L" => splitNodalTorusToCurve a
local notation "s" => PrincipalOpenTransport.inclusion (slopePolynomial (a : K))
local notation "m" => Spec.map (CommRingCat.ofHom (slopeLaurentMap a).toRingHom)

/-- The original affine normalization agrees with the entire Laurent chart on their overlap. -/
theorem splitNormalization_slope_overlap : s ≫ F = m ≫ L := by
  let f : Coordinate W 2 →ₐ[K] SlopeOpen (a : K) :=
    (IsScalarTower.toAlgHom K K[X] (SlopeOpen (a : K))).comp
      (splitNormalizationChart W rfl rfl rfl rfl)
  have hc : algebraMap K[X] (SlopeOpen (a : K)) (C (a : K)) =
      algebraMap K (SlopeOpen (a : K)) (a : K) :=
    (IsScalarTower.algebraMap_apply K K[X] (SlopeOpen (a : K)) (a : K)).symm
  change Spec.map _ ≫ Spec.map _ ≫ integralCurveChart W 2 = _
  rw [← Spec.map_comp_assoc]
  exact slopeLaurentMap_toCurve a f
    (by simp [f, splitNormalizationChart_coord, slopeZ, splitNodalEquation, hc])
    (by simp [f, splitNormalizationChart_coord, slopeZ, splitNodalEquation, hc])

/-- Gluing the full original affine and Laurent formulas produces a complete cubic map. -/
@[irreducible] def splitNormalizationFromCharts : scheme K ⟶ integralCurve W :=
  (infinityTorus_isPushout a).desc F L (splitNormalization_slope_overlap a)

/-- The gluing retains the complete affine normalization, including both node origins. -/
@[reassoc] theorem splitNormalizationFromCharts_left :
    left K ≫ splitNormalizationFromCharts a = F := by
  rw [splitNormalizationFromCharts]
  exact (infinityTorus_isPushout a).inl_desc _ _ _

/-- The gluing retains the entire original infinity torus. -/
@[reassoc] theorem splitNormalizationFromCharts_infinity :
    infinityTorusChart a ≫ splitNormalizationFromCharts a = L := by
  rw [splitNormalizationFromCharts]
  exact (infinityTorus_isPushout a).inr_desc _ _ _

/-- Both chart formulas retain the same original coefficient map on the complete line. -/
@[reassoc] theorem splitNormalizationFromCharts_base :
    splitNormalizationFromCharts a ≫ integralCurveStructure W = toBase K := by
  apply (infinityTorus_isPushout a).hom_ext
  · rw [splitNormalizationFromCharts_left_assoc, splitAffineToCubic_base]
  · rw [splitNormalizationFromCharts_infinity_assoc, splitNodalTorusToCurve,
      Category.assoc, integralCurveChart_structure, splitNodalTorusIso_structure,
      infinityTorusChart_toBase]
    rfl

/-- Proper-extension uniqueness identifies the explicit two-chart normalization. -/
theorem splitNormalizationFromCharts_eq : splitNormalizationFromCharts a = N :=
  splitCompleteNormalization_unique W rfl rfl rfl rfl _
    (splitNormalizationFromCharts_base a) (splitNormalizationFromCharts_left a)

/-- The existing complete normalization retains every function of the full infinity chart. -/
@[reassoc] theorem splitCompleteNormalization_infinity : infinityTorusChart a ≫ N = L := by
  rw [← splitNormalizationFromCharts_eq, splitNormalizationFromCharts_infinity]

/-- The entire original infinity chart factors through the complete normalization. -/
@[reassoc] theorem splitCompleteNormalization_infinity_section :
    (splitNodalTorusIso a).inv ≫ infinityTorusChart a ≫ N = integralCurveChart W 1 := by
  rw [splitCompleteNormalization_infinity, splitNodalTorusToCurve, Iso.inv_hom_id_assoc]

end FLT.Mazur

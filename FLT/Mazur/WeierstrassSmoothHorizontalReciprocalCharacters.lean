/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothHorizontalLaurentEvaluation

public import FLT.Mazur.PolygonScaledReciprocal

/-!
# Characters in the retained line's reciprocal coordinate

Evaluating after the signed reciprocal changes the smooth character to its
inverse. The constant tangent scale is retained as a unit over the residue base.
-/

@[expose] public noncomputable section
open IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R
local notation "L" => K[T;T⁻¹]
local notation "C" => SmoothHorizontalResidueRing D
local notation "j" => smoothHorizontalResidueConic D

/-- Laurent evaluation transports the entire signed reciprocal, including negative powers. -/
theorem smoothHorizontalLaurentEvaluation_reciprocal (q : Cˣ) (scale : Kˣ) :
    (smoothHorizontalLaurentEvaluation D q).comp
      (PolygonScaledReciprocal.reciprocal scale) =
    smoothHorizontalLaurentEvaluation D (Units.map (algebraMap K C) scale * q⁻¹) := by
  apply AlgHom.coe_ringHom_injective
  apply PolygonScalingNaturality.ringHom_ext
  · intro r
    simp only [AlgHom.coe_toRingHom, AlgHom.comp_apply,
      PolygonScaledReciprocal.reciprocal_C, smoothHorizontalLaurentEvaluation_C]
  · simp only [AlgHom.coe_toRingHom, AlgHom.comp_apply,
      PolygonScaledReciprocal.reciprocal_T, map_mul, smoothHorizontalLaurentEvaluation_C,
      smoothHorizontalLaurentEvaluation_T, zpow_neg_one, zpow_one, Units.val_mul, Units.coe_map]
    rfl
  · simp only [AlgHom.coe_toRingHom, AlgHom.comp_apply,
      PolygonScaledReciprocal.reciprocal_T_inv, map_mul, smoothHorizontalLaurentEvaluation_C,
      smoothHorizontalLaurentEvaluation_T, zpow_one, zpow_neg_one,
      mul_inv_rev, inv_inv, Units.val_mul, ← map_inv, Units.coe_map]
    exact mul_comm _ _

/-- The reciprocal first-line coordinate transforms by the inverse smooth character. -/
theorem smoothHorizontalFirstLine_character (scale : Kˣ) :
    Units.map (algebraMap K C) scale *
        (smoothHorizontalTangentUnit D * smoothHorizontalConicUnit D)⁻¹ =
      (smoothHorizontalTangentUnit D)⁻¹ *
        (Units.map (algebraMap K C) scale * (smoothHorizontalConicUnit D)⁻¹) := by
  simp only [mul_inv_rev]
  ac_rfl

/-- The opposite reciprocal line coordinate transforms by the positive smooth character. -/
theorem smoothHorizontalSecondLine_character (scale : Kˣ) :
    Units.map (algebraMap K C) scale *
        ((smoothHorizontalTangentUnit D)⁻¹ * smoothHorizontalConicUnit D)⁻¹ =
      smoothHorizontalTangentUnit D *
        (Units.map (algebraMap K C) scale * (smoothHorizontalConicUnit D)⁻¹) := by
  simp only [mul_inv_rev, inv_inv]
  ac_rfl

end FLT.Mazur.WeierstrassIntegralChart

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFixedRetained
public import FLT.Mazur.WeierstrassRetainedFixedNaturality
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedPolygon

/-!
# Original quotient squares at every fixed retained label

Compatible unit quotients give compatible full corrections at all depths.
The maps use the original labeled atlas arrows and normalized polygon arrow.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m k : ℕ) (hk : k ≤ n)
  (q : (Quotient R π m)ˣ) (q₁ : (Quotient R π (m + 1))ˣ)
  (hq : parameter R π m * (q : Quotient R π m) =
    arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ start) π m)
  (hq₁ : parameter R π (m + 1) * (q₁ : Quotient R π (m + 1)) =
    arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ start) π (m + 1))
  (hqq : Units.map (restriction R π m).toMonoidHom q₁ = q)
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ start) π m
local notation "τ₁" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ start) π (m + 1)
local notation "F" => ringMap (AlgHom.toRingHom (restriction R π m)) (parameter R π (m + 1))
  (parameter R π m) (restriction_parameter R π m)
local notation "V" => arithmeticRetainedFullCorrection data H m k hk
local notation "V₁" => arithmeticRetainedFullCorrection data H (m + 1) k hk

omit [IsBezout R] in
include hqq in
/-- Every original retained atlas label commutes with the full arithmetic quotient square. -/
@[reassoc] theorem arithmeticFixedRetainedMap_restriction (a : Fin k) (b : Bool) :
    arithmeticFixedRetainedMap hπ data H m k hk q hq a b ≫
      arithmeticFactorRatioPolygonRestriction π m W (π ^ start) H.a1_unit H.scale_div k =
    arithmeticLabeledAtlasRestriction hπ data H m k hk (.retained a b) ≫
      arithmeticFixedRetainedMap hπ data H (m + 1) k hk q₁ hq₁ a b := by
  let _ : Fact (IsNilpotent τ) := ⟨arithmeticInitialFactorRatioSmoothing_nilpotent
    W H.a1_unit (π ^ start) π m H.scale_div⟩
  let _ : Fact (IsNilpotent τ₁) := ⟨arithmeticInitialFactorRatioSmoothing_nilpotent
    W H.a1_unit (π ^ start) π (m + 1) H.scale_div⟩
  have hu : Units.map (F).toMonoidHom
      (retainedScaledCorrectionUnit (parameter R π (m + 1))
        (retainedDepthScale q₁ 1 a.val) (V₁ a)) =
      retainedScaledCorrectionUnit (parameter R π m) (retainedDepthScale q 1 a.val) (V a) := by
    rw [retainedScaledCorrectionUnit_coefficients (restriction R π m).toRingHom
      (parameter R π (m + 1)) (parameter R π m) (restriction_parameter R π m)
      (V₁ a) (V a) (arithmeticRetainedFullCorrection_restriction data H m k hk a),
      retainedDepthScale_map, map_one, hqq]
  have hc := retainedFixedSmoothingChart_coefficients (restriction R π m).toRingHom
    (parameter R π (m + 1)) τ₁ (q₁ : Quotient R π (m + 1)) hq₁
    (parameter R π m) τ (q : Quotient R π m) (restriction_parameter R π m)
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ start) π m)
    (congrArg Units.val hqq) hq _ _ hu
  unfold arithmeticFixedRetainedMap retainedFixedPolygonMap
    arithmeticFactorRatioPolygonRestriction
  rw [Category.assoc, retainedPolygonMap_parameterProjection, ← Category.assoc, ← hc]
  change _ = arithmeticPolygonNodeRestriction R π m ≫ _
  rw [arithmeticRetainedPolygonRestriction_eq, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth

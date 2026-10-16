/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedFixedPolygon
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedCorrectionFamily
public import FLT.Mazur.WeierstrassDividedArithmeticFirstRetainedFactorRatio

/-!
# Corrected maps at all original arithmetic retained labels

One unit quotient determines one normalized target polygon. Each depth uses
its own full roots, with the coefficient scale supplied by the recurrence.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m k : ℕ) (hk : k ≤ n)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ start) π m
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ start) π m H.scale_div)
variable (q : (Quotient R π m)ˣ)
  (hq : parameter R π m * (q : Quotient R π m) =
    arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ start) π m)

/-- The full comparison at every actual retained atlas object and both branch labels. -/
def arithmeticFixedRetainedMap (a : Fin k) (b : Bool) :
    arithmeticLabeledAtlasObject hπ data H m k hk (.retained a b) ⟶
      arithmeticFactorRatioPolygon π m W (π ^ start) H.a1_unit H.scale_div k := by
  let _ := hn
  exact retainedFixedPolygonMap (parameter R π m) τ q hq 1 k
    (arithmeticRetainedFullCorrection data H m k hk a) a b

omit [IsBezout R] in
/-- The actual consecutive retained maps agree along their entire original shared edge. -/
@[reassoc] theorem arithmeticFixedRetainedMap_adjacent (a : ℕ) (ha : a + 1 < k)
    (b : Bool) :
    leftBranchOpen Q (parameter R π m) ≫
        arithmeticFixedRetainedMap hπ data H m k hk q hq ⟨a, by omega⟩ b =
      precedingBranch Q (parameter R π m) ≫
        arithmeticFixedRetainedMap hπ data H m k hk q hq ⟨a + 1, ha⟩ b := by
  let _ := hn
  exact retainedFixedPolygonMap_adjacent (parameter R π m) τ q hq 1 k a ha _ _
    (arithmeticRetainedFullCorrection_adjacent data H m k hk hπ a ha) b

omit [IsBezout R] in
/-- The first corrected node recovers the original full factor-ratio comparison. -/
theorem arithmeticFixedRetainedMap_first (hk0 : 0 < k)
    (hqq : (q : Q) =
      (↑(zeroInitialTangentUnit (W.map (algebraMap R Q))
        (H.a1_unit.map (algebraMap R Q)))⁻¹ : Q) ^ 2 *
          algebraMap R Q (Classical.choose H.scale_div)) (b : Bool) :
    arithmeticFixedRetainedMap hπ data H m k hk q hq ⟨0, hk0⟩ b =
      arithmeticFactorRatioFirstRetainedMap hπ data H m k hk hk0 b := by
  unfold arithmeticFixedRetainedMap retainedFixedPolygonMap
    arithmeticFactorRatioFirstRetainedMap arithmeticRetainedFactorRatioChart
  rw [retainedDepthScale_zero]
  simp only [retainedScaledCorrectionUnit, map_one, one_mul]
  unfold retainedFixedSmoothingChart retainedFactorRatioChart
  rw [retainedFactorRatioEvaluation_eq_fixed]
  congr 3
  apply congrArg AlgHom.toRingHom
  apply chartRing_hom_ext
  · erw [retainedFixedSmoothingEvaluation_left, retainedFixedSmoothingEvaluation_left]
    rw [hqq]
    rfl
  · erw [retainedFixedSmoothingEvaluation_right, retainedFixedSmoothingEvaluation_right]
    rfl

end FLT.Mazur.WeierstrassDividedDepth

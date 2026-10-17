/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdEarlierInitial
public import FLT.Mazur.WeierstrassDividedSecondPrecedingInitial

/-!
# The full third predecessor boundary at depth one

The original initial chart is attached to the corrected predecessor with
both old and new opposite factors. Its missing initial correction must use
this complete boundary, including the original Laurent parameter.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticThirdAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticSecondJointAtlasChart hπ data H m j hj u hu
local notation "χ" => changedArithmeticAtlasChart hπ data H m j hj u hu
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "P" => arithmeticInitialPunctureInclusion π m W (π ^ 1) H.a1_unit H.scale_div
local notation "E" => arithmeticInitialPunctureIso π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "B" => arithmeticRetainedRightParameter data H m j hj (Fin.mk 0 (Nat.zero_lt_succ j))
local notation "s" => arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m

local notation "s₂" => arithmeticSecondPrecedingSmoothing hπ data H m j hj u hu
local notation "C" => arithmeticThirdPrecedingIso hπ data H m j hj u hu
local notation "V" => arithmeticThirdPrecedingIntegralField hπ data H j hj u hu

omit [IsBezout R] in
/-- The predecessor's direct right puncture keeps both full smoothing parameters. -/
@[reassoc] theorem arithmeticThirdPrecedingIso_right (b : Bool) :
    rightBranchOpen Q (s₂ b) ≫ (C b).hom =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s₂ b) (V b) false)).hom ≫
        rightBranchOpen Q (s b) := by
  simpa only [punctureOpen_false] using
    arithmeticThirdPrecedingIso_puncture hπ data H m j hj u hu b false

variable (ha : 1 = j)
local notation "M" => arithmeticThirdPrecedingIdentification hπ data H m j hj u hu 0 ha
local notation "M₂" => arithmeticSecondJointPrecedingIdentification hπ data H m j hj u hu 0 ha

/-- The installed predecessor has its complete right boundary after the third correction. -/
@[reassoc] theorem arithmeticThirdPreceding_right (b : Bool) :
    rightBranchOpen Q (s₂ b) ≫ (M₂ b).hom ≫ κ (.retained ⟨0, by omega⟩ b) =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s₂ b) (V b) false)).hom ≫
        rightBranchOpen Q (s b) ≫ (M b).hom ≫ ι (.retained ⟨0, by omega⟩ b) := by
  rw [← arithmeticThirdPreceding_chart hπ data H m j hj u hu 0 ha b]
  rw [arithmeticThirdPrecedingIso_right_assoc]

/-- The depth-one initial edge retains the original parameter and both opposite corrections. -/
@[reassoc] theorem arithmeticThirdAtlas_preceding_initial (b : Bool) :
    P ≫ ι (.initial b) = (E).inv ≫ B ≫
      (punctureSpecIso (arithmeticSecondPrecedingOpposite hπ data H m j hj u hu b)).hom ≫
        (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s₂ b) (V b) false)).hom ≫
          rightBranchOpen Q (s b) ≫ (M b).hom ≫
            ι (.retained ⟨0, Nat.zero_lt_succ j⟩ b) := by
  rw [arithmeticThirdAtlasChart_initial,
    ← arithmeticSecondJointAtlasChart_initial hπ data H m j hj u hu b,
    arithmeticSecondJointAtlas_preceding_initial hπ data H m j hj u hu ha b,
    arithmeticThirdPreceding_right]

end FLT.Mazur.WeierstrassDividedDepth

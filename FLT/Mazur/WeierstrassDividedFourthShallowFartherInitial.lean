/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthFartherInitial
public import FLT.Mazur.WeierstrassDividedFourthShallowUnchanged
public import FLT.Mazur.WeierstrassDividedThirdEarlierInitial

/-!
# Retain the depth-three initial boundary in the depth-two corrected atlas

At depth three the farther node meets the original initial open. Its direct
right parameter and full original base are retained explicitly.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthOuterAtlasChart arithmeticFourthOuterIso
  arithmeticThirdAtlasChart arithmeticThirdInitialAtlasChart
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
local notation "s" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m

variable (ha : 3 = j)
local notation "D₄" => arithmeticFourthFartherIdentification hπ data H m j hj u hu 0 ha
local notation "ω" => arithmeticFourthShallowAtlasChart hπ data H m j hj u hu
local notation "χ₄" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "E₄" => arithmeticFourthOuterAtlasCorrection hπ data H m j hj u hu
local notation "s₄" => arithmeticFourthFartherSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticFourthFartherIntegralField hπ data H j hj u hu

/-- The depth-three initial label keeps the entire previous full initial open. -/
def arithmeticFourthShallowThreeInitialUnchanged (b : Bool) :
    arithmeticFourthOuterAtlasObject hπ data H m j hj u hu (.initial b) ≅
      arithmeticFourthShallowAtlasObject hπ data H m j hj u hu (.initial b) :=
  eqToIso (by simp only [arithmeticFourthShallowAtlasObject, show ¬j = 2 by omega, ↓reduceIte])

/-- The unchanged initial label retains its previous global inclusion. -/
@[reassoc] theorem arithmeticFourthShallowThreeInitialUnchanged_chart (b : Bool) :
    (arithmeticFourthShallowThreeInitialUnchanged hπ data H m j hj u hu ha b).hom ≫
      ω (.initial b) = χ₄ (.initial b) := by
  apply (cancel_epi (E₄ (.initial b)).hom).mp
  rw [← Category.assoc, ← Iso.trans_hom]
  have h := arithmeticFourthShallowAtlasCorrection_chart hπ data H m j hj u hu (.initial b)
  simpa only [arithmeticFourthShallowAtlasCorrection, show ¬j = 2 by omega, ↓reduceDIte,
    arithmeticFourthShallowThreeInitialUnchanged,
    arithmeticFourthOuterAtlasCorrection_chart] using h

/-- The complete original initial source remains identified with its actual depth-three label. -/
def arithmeticFourthShallowInitialThreeIdentification (b : Bool) :
    arithmeticThirdAtlasObject hπ data H m j hj u hu (.initial b) ≅
      arithmeticFourthShallowAtlasObject hπ data H m j hj u hu (.initial b) :=
  arithmeticFourthOuterInitialThreeIdentification hπ data H m j hj u hu ha b ≪≫
    arithmeticFourthShallowThreeInitialUnchanged hπ data H m j hj u hu ha b

/-- The depth-three farther node retains its complete positive factor. -/
def arithmeticFourthShallowFartherThreeIdentification (b : Bool) :
    PolygonSmoothing.chart Q (s₄ b) ≅
      arithmeticFourthShallowAtlasObject hπ data H m j hj u hu
        (.retained ⟨0, Nat.zero_lt_succ j⟩ b) :=
  D₄ b ≪≫ arithmeticFourthShallowUnchangedIdentification hπ data H m j hj u hu
    ⟨0, Nat.zero_lt_succ j⟩ (by omega) b

local notation "J" => arithmeticFourthShallowInitialThreeIdentification hπ data H m j hj u hu ha
local notation "D" => arithmeticFourthShallowFartherThreeIdentification hπ data H m j hj u hu ha

/-- The depth-three initial edge retains its full original base and direct compensation. -/
@[reassoc] theorem arithmeticFourthShallowAtlas_farther_initial (b : Bool) :
    P ≫ (J b).hom ≫ ω (.initial b) = (E).inv ≫ B ≫
      (punctureSpecIso (correctionPunctureFactor R π m
        (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m) (V b) false)).hom ≫
        rightBranchOpen Q (s₄ b) ≫ (D b).hom ≫
          ω (.retained ⟨0, Nat.zero_lt_succ j⟩ b) := by
  simpa only [arithmeticFourthShallowInitialThreeIdentification,
    arithmeticFourthShallowFartherThreeIdentification, Iso.trans_hom, Category.assoc,
    arithmeticFourthShallowThreeInitialUnchanged_chart,
    arithmeticFourthShallowUnchanged_chart] using
      arithmeticFourthOuterAtlas_farther_initial hπ data H m j hj u hu ha b

omit m in
/-- At layer four this boundary retains precisely its original full initial base. -/
@[reassoc] theorem arithmeticFourthShallowAtlas_farther_initial_fourth (b : Bool) :
    arithmeticInitialPunctureInclusion π 4 W (π ^ 1) H.a1_unit H.scale_div ≫
      (arithmeticFourthShallowInitialThreeIdentification hπ data H 4 j hj u hu ha b).hom ≫
        arithmeticFourthShallowAtlasChart hπ data H 4 j hj u hu (.initial b) =
      (arithmeticInitialPunctureIso π 4 W (π ^ 1)
        (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
          (H.b3_div _) (H.b4_div _) (H.b6_div _)).inv ≫
        arithmeticRetainedRightParameter data H 4 j hj ⟨0, Nat.zero_lt_succ j⟩ ≫
          rightBranchOpen (Quotient R π 4)
            (arithmeticFourthFartherSmoothing hπ data H j hj u hu 4 b) ≫
          (arithmeticFourthShallowFartherThreeIdentification hπ data H 4 j hj u hu ha b).hom ≫
            arithmeticFourthShallowAtlasChart hπ data H 4 j hj u hu
              (.retained ⟨0, Nat.zero_lt_succ j⟩ b) := by
  simpa only [arithmeticFourthShallowInitialThreeIdentification,
    arithmeticFourthShallowFartherThreeIdentification, Iso.trans_hom, Category.assoc,
    arithmeticFourthShallowThreeInitialUnchanged_chart,
    arithmeticFourthShallowUnchanged_chart] using
      arithmeticFourthOuterAtlas_farther_initial_fourth hπ data H j hj u hu ha b

end FLT.Mazur.WeierstrassDividedDepth

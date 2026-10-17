/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthDeepInitial

/-!
# Unchanged initial and retained edges before the fifth deep chain

At depth greater than four the original initial edge remains untouched.
Retained edges wholly before the corrected chain keep their exact original maps.
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
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (hj₄ : 4 ≤ j)
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

local notation "ω" => arithmeticFifthDeepAtlasChart hπ data H m j hj u hu hj₄
local notation "s₄" => arithmeticFifthDeepEarlierSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticFifthDeepEarlierIntegralField hπ data H j hj u hu

local notation "J" => arithmeticFifthDeepInitialIdentification hπ data H m j hj u hu hj₄
local notation "N" => arithmeticFifthDeepBeforeIdentification hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m

/-- At depth greater than four the full original initial edge is unchanged at every order. -/
@[reassoc] theorem arithmeticFifthDeepAtlas_before_initial (hj₅ : 4 < j) (b : Bool) :
    P ≫ (J b).hom ≫ ω (.initial b) = (E).inv ≫ B ≫ rightBranchOpen Q τ ≫
      (O b).hom ≫ (N ⟨0, Nat.zero_lt_succ j⟩ hj₅ b).hom ≫
        ω (.retained ⟨0, Nat.zero_lt_succ j⟩ b) := by
  rw [arithmeticFifthDeepAtlasChart_original_initial, arithmeticThirdAtlasChart_initial,
    arithmeticFifthDeepBefore_chart]
  exact changedArithmeticAtlas_normalized_initial hπ data H m j hj u hu b

/-- Edges wholly before the fifth corrections retain both original normalized branches. -/
@[reassoc] theorem arithmeticFifthDeepAtlas_before_adjacent
    (a : ℕ) (ha : a + 5 < j) (b : Bool) :
    leftBranchOpen Q τ ≫ (O b).hom ≫
        (N ⟨a, by omega⟩ (show a + 4 < j by omega) b).hom ≫
          ω (.retained ⟨a, by omega⟩ b) =
      precedingBranch Q τ ≫ (O b).hom ≫
        (N ⟨a + 1, by omega⟩ (show a + 1 + 4 < j by omega) b).hom ≫
          ω (.retained ⟨a + 1, by omega⟩ b) := by
  rw [arithmeticFifthDeepBefore_chart, arithmeticFifthDeepBefore_chart]
  exact changedArithmeticAtlas_normalized_adjacent hπ data H m j hj u hu a (by omega) b

end FLT.Mazur.WeierstrassDividedDepth

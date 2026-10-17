/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthFartherIncoming
public import FLT.Mazur.WeierstrassDividedThirdEarlierInitial

/-!
# The original initial boundary of the farther fourth factor

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
local notation "D" => arithmeticFourthFartherIdentification hπ data H m j hj u hu 0 ha
local notation "ω" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "s₄" => arithmeticFourthFartherSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticFourthFartherIntegralField hπ data H j hj u hu

/-- At depth three the installed initial label is the full original initial open. -/
def arithmeticFourthOuterInitialThreeIdentification (b : Bool) :
    arithmeticThirdAtlasObject hπ data H m j hj u hu (.initial b) ≅
      arithmeticFourthOuterAtlasObject hπ data H m j hj u hu (.initial b) :=
  eqToIso (by simp only [arithmeticFourthOuterAtlasObject, arithmeticFourthInitialAtlasObject,
    show ¬j = 1 by omega, ↓reduceIte, arithmeticFourthAtlasObject,
    arithmeticThirdInitialAtlasObject])

local notation "J" => arithmeticFourthOuterInitialThreeIdentification hπ data H m j hj u hu ha

/-- The identification retains the original full initial inclusion at depth three. -/
@[reassoc] theorem arithmeticFourthOuterAtlasChart_initial_three (b : Bool) :
    (J b).hom ≫ ω (.initial b) = ι (.initial b) := by
  have h := arithmeticFourthOuterAtlasCorrection_chart hπ data H m j hj u hu (.initial b)
  have hh := congrArg (fun f ↦
    (arithmeticThirdInitialAtlasCorrection hπ data H m j hj u hu (.initial b)).hom ≫ f) h
  rw [arithmeticThirdInitialAtlasCorrection_chart] at hh
  simpa only [arithmeticFourthOuterAtlasCorrection, arithmeticFourthInitialAtlasCorrection,
    arithmeticThirdInitialAtlasCorrection, show ¬j = 1 by omega, ↓reduceDIte,
    arithmeticFourthAtlasCorrection, arithmeticFourthOuterInitialThreeIdentification,
    Iso.trans_hom, Iso.refl_hom, Category.id_comp, eqToIso.hom,
    ← Category.assoc, eqToHom_trans] using hh

/-- The depth-three initial edge retains its full original base and direct compensation. -/
@[reassoc] theorem arithmeticFourthOuterAtlas_farther_initial (b : Bool) :
    P ≫ (J b).hom ≫ ω (.initial b) = (E).inv ≫ B ≫
      (punctureSpecIso (correctionPunctureFactor R π m
        (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m) (V b) false)).hom ≫
        rightBranchOpen Q (s₄ b) ≫ (D b).hom ≫
          ω (.retained ⟨0, Nat.zero_lt_succ j⟩ b) := by
  rw [arithmeticFourthOuterAtlasChart_initial_three hπ data H m j hj u hu ha b,
    arithmeticThirdAtlasChart_initial,
    changedArithmeticAtlas_normalized_initial hπ data H m j hj u hu b]
  have h := arithmeticFourthFartherIso_puncture hπ data H j hj u hu m b false
  simp only [punctureOpen_false] at h
  rw [← Category.assoc _ (rightBranchOpen Q (s₄ b)), ← h, Category.assoc,
    arithmeticFourthFarther_original_chart]

omit m in
/-- At layer four this boundary retains precisely its original full initial base. -/
@[reassoc] theorem arithmeticFourthOuterAtlas_farther_initial_fourth (b : Bool) :
    arithmeticInitialPunctureInclusion π 4 W (π ^ 1) H.a1_unit H.scale_div ≫
      (arithmeticFourthOuterInitialThreeIdentification hπ data H 4 j hj u hu ha b).hom ≫
        arithmeticFourthOuterAtlasChart hπ data H 4 j hj u hu (.initial b) =
      (arithmeticInitialPunctureIso π 4 W (π ^ 1)
        (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
          (H.b3_div _) (H.b4_div _) (H.b6_div _)).inv ≫
        arithmeticRetainedRightParameter data H 4 j hj ⟨0, Nat.zero_lt_succ j⟩ ≫
          rightBranchOpen (Quotient R π 4)
            (arithmeticFourthFartherSmoothing hπ data H j hj u hu 4 b) ≫
          (arithmeticFourthFartherIdentification hπ data H 4 j hj u hu 0 ha b).hom ≫
            arithmeticFourthOuterAtlasChart hπ data H 4 j hj u hu
              (.retained ⟨0, Nat.zero_lt_succ j⟩ b) := by
  have h := arithmeticFourthOuterAtlas_farther_initial hπ data H 4 j hj u hu ha b
  have hi := arithmeticFourthFartherOppositeEquiv_fourth hπ data H j hj u hu b
  change correctionPunctureFactor R π 4 _ (V b) false = AlgEquiv.refl at hi
  rw [hi, punctureSpecIso_refl, Iso.refl_hom] at h
  simpa only [branchTorus, Category.id_comp] using h

end FLT.Mazur.WeierstrassDividedDepth

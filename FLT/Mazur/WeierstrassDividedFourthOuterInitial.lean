/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthOuterIdentification
public import FLT.Mazur.WeierstrassDividedThirdEarlierInitial

/-!
# The full shallow initial edge after the outer fourth replacement

At depth two the earlier node meets the original initial open. Its direct
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

variable (ha : 2 = j)
local notation "M" => arithmeticThirdEarlierIdentification hπ data H m j hj u hu 0 ha
local notation "D" => arithmeticFourthOuterIdentification hπ data H m j hj u hu 0 ha
local notation "ω" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "s₄" => arithmeticFourthOuterSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticFourthOuterIntegralField hπ data H j hj u hu

/-- At depth two the installed initial label is the full original initial open. -/
def arithmeticFourthOuterInitialTwoIdentification (b : Bool) :
    arithmeticThirdAtlasObject hπ data H m j hj u hu (.initial b) ≅
      arithmeticFourthOuterAtlasObject hπ data H m j hj u hu (.initial b) :=
  eqToIso (by simp only [arithmeticFourthOuterAtlasObject, arithmeticFourthInitialAtlasObject,
    show ¬j = 1 by omega, ↓reduceIte, arithmeticFourthAtlasObject,
    arithmeticThirdInitialAtlasObject])

local notation "J" => arithmeticFourthOuterInitialTwoIdentification hπ data H m j hj u hu ha

/-- The identification retains the original full initial inclusion at depth two. -/
@[reassoc] theorem arithmeticFourthOuterAtlasChart_initial_two (b : Bool) :
    (J b).hom ≫ ω (.initial b) = ι (.initial b) := by
  have h := arithmeticFourthOuterAtlasCorrection_chart hπ data H m j hj u hu (.initial b)
  have hh := congrArg (fun f ↦
    (arithmeticThirdInitialAtlasCorrection hπ data H m j hj u hu (.initial b)).hom ≫ f) h
  rw [arithmeticThirdInitialAtlasCorrection_chart] at hh
  simpa only [arithmeticFourthOuterAtlasCorrection, arithmeticFourthInitialAtlasCorrection,
    arithmeticThirdInitialAtlasCorrection, show ¬j = 1 by omega, ↓reduceDIte,
    arithmeticFourthAtlasCorrection, arithmeticFourthOuterInitialTwoIdentification,
    Iso.trans_hom, Iso.refl_hom, Category.id_comp, eqToIso.hom,
    ← Category.assoc, eqToHom_trans] using hh

/-- The shallow edge uses the complete original initial base and both direct compensations. -/
@[reassoc] theorem arithmeticFourthOuterAtlas_earlier_initial (b : Bool) :
    P ≫ (J b).hom ≫ ω (.initial b) = (E).inv ≫ B ≫
      (punctureSpecIso (correctionPunctureFactor R π m
        (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m)
        (arithmeticThirdEarlierIntegralField hπ data H j hj u hu b) false)).hom ≫
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s b) (V b) false)).hom ≫
        rightBranchOpen Q (s₄ b) ≫ (D b).hom ≫
          ω (.retained ⟨0, Nat.zero_lt_succ j⟩ b) := by
  rw [arithmeticFourthOuterAtlasChart_initial_two hπ data H m j hj u hu ha b]
  rw [arithmeticThirdAtlas_earlier_initial hπ data H m j hj u hu ha b]
  have h := arithmeticFourthOuterIso_puncture hπ data H j hj u hu m b false
  simp only [punctureOpen_false] at h
  rw [← Category.assoc _ (rightBranchOpen Q (s₄ b)), ← h, Category.assoc,
    arithmeticFourthOuter_chart, arithmeticThirdInitialAtlasChart_retained]

end FLT.Mazur.WeierstrassDividedDepth

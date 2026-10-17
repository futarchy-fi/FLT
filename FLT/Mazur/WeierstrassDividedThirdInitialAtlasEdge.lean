/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdInitialAtlas
public import FLT.Mazur.WeierstrassDividedThirdPrecedingInitial

/-!
# The full depth-one edge of the corrected original initial atlas

The exact residual contains the original Mobius parameter and retained right
parameter, as well as all three full node factors. No identity is asserted
for this residual before its parameter comparison has been proved.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticThirdInitialAtlasChart arithmeticThirdAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "C" => arithmeticThirdInitialIso hπ data H m j hj u hu
local notation "ι" => arithmeticThirdInitialAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticThirdAtlasChart hπ data H m j hj u hu
local notation "A" => arithmeticThirdInitialAtlasObject hπ data H m j hj u hu
local notation "E" => arithmeticThirdInitialAtlasCorrection hπ data H m j hj u hu
local notation "V" => arithmeticThirdEarlierIntegralField hπ data H j hj u hu
local notation "s₂" => arithmeticSecondPrecedingSmoothing hπ data H m j hj u hu
local notation "P" => arithmeticThirdPrecedingIntegralField hπ data H j hj u hu

/-- The residual keeps the entire original initial parameter before every full correction. -/
def arithmeticThirdInitialResidual (b : Bool) : branchTorus Q ⟶ branchTorus Q :=
  (punctureSpecIso (correctionPunctureFactor R π m τ (V b) true)).inv ≫
    (arithmeticInitialMobiusParameter π m W (π ^ 1)
      (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
        (H.b3_div _) (H.b4_div _) (H.b6_div _)).inv ≫
      arithmeticRetainedRightParameter data H m j hj ⟨0, Nat.zero_lt_succ j⟩ ≫
        (punctureSpecIso (arithmeticSecondPrecedingOpposite hπ data H m j hj u hu b)).hom ≫
          (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s₂ b) (P b) false)).hom

variable (ha : 1 = j)

/-- Identify the installed depth-one initial label with the constructed full corrected open. -/
def arithmeticThirdInitialIdentification (b : Bool) :
    arithmeticThirdInitialObject hπ data H m j hj u hu b ≅ A (.initial b) :=
  eqToIso (by simp only [arithmeticThirdInitialAtlasObject, ha.symm, ↓reduceIte])

local notation "J" => arithmeticThirdInitialIdentification hπ data H m j hj u hu ha

omit [IsBezout R] in
/-- The actual initial correction is the constructed full-chart isomorphism. -/
theorem arithmeticThirdInitialAtlasCorrection_initial (b : Bool) :
    E (.initial b) = C b ≪≫ J b := by
  simp only [arithmeticThirdInitialAtlasCorrection, show j = 1 from ha.symm, ↓reduceDIte]
  rfl

/-- The installed full initial comparison recovers the original third-atlas inclusion. -/
@[reassoc] theorem arithmeticThirdInitial_chart (b : Bool) :
    (C b).hom ≫ (J b).hom ≫ ι (.initial b) = κ (.initial b) := by
  have h := arithmeticThirdInitialAtlasCorrection_chart hπ data H m j hj u hu (.initial b)
  rw [arithmeticThirdInitialAtlasCorrection_initial hπ data H m j hj u hu ha b] at h
  simpa only [Iso.trans_hom, Category.assoc] using h

local notation "M" => arithmeticThirdPrecedingIdentification hπ data H m j hj u hu 0 ha
local notation "s" => arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m

/-- The actual corrected depth-one edge has exactly the full residual defined above. -/
@[reassoc] theorem arithmeticThirdInitialAtlas_residual_initial (b : Bool) :
    arithmeticThirdInitialPuncture hπ data H m j hj u hu b ≫ (J b).hom ≫ ι (.initial b) =
      arithmeticThirdInitialResidual hπ data H m j hj u hu b ≫
        rightBranchOpen Q (s b) ≫ (M b).hom ≫ ι (.retained ⟨0, by omega⟩ b) := by
  simp only [arithmeticThirdInitialPuncture, Category.assoc, arithmeticThirdInitial_chart,
    arithmeticThirdInitialAtlasChart_retained]
  rw [arithmeticThirdAtlas_preceding_initial hπ data H m j hj u hu ha b,
    arithmeticInitialNormalizedPunctureIso_inv_comp_assoc]
  simp only [arithmeticThirdInitialResidual, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth

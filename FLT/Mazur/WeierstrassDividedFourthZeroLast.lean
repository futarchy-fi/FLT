/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthZeroInitial
public import FLT.Mazur.WeierstrassDividedFourthAtlasIdentification
public import FLT.Mazur.WeierstrassDividedThirdAtlasIdentification
public import FLT.Mazur.WeierstrassDividedSecondJointAtlasClosing
public import FLT.Mazur.WeierstrassDividedResidualLiftAtlasEdges

/-!
# The full accumulated last factor at the depth-zero boundary

Compose all four actual last-node corrections before identifying the original
initial overlap. No predecessor or cancellation assumption is introduced.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthOuterAtlasChart arithmeticThirdAtlasChart
  arithmeticFourthLastOrientedIso arithmeticThirdLastOrientedIso
  arithmeticSecondJointOrientedIso arithmeticResidualLiftOrientedIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "ω" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "κ" => changedArithmeticAtlasChart hπ data H m j hj u hu
local notation "N" => arithmeticFourthOuterLastIdentification hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m

/-- The full last-node comparison includes every correction already installed. -/
def arithmeticFourthAccumulatedLastIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q τ :=
  arithmeticResidualLiftOrientedIso hπ data H m j hj u hu b ≪≫
    arithmeticSecondJointOrientedIso hπ data H m j hj u hu b ≪≫
      arithmeticThirdLastOrientedIso hπ data H m j hj u hu b ≪≫
        arithmeticFourthLastOrientedIso hπ data H m j hj u hu b

local notation "C" => arithmeticFourthAccumulatedLastIso hπ data H m j hj u hu

/-- The accumulated comparison recovers the original normalized last inclusion. -/
@[reassoc] theorem arithmeticFourthAccumulatedLast_chart (b : Bool) :
    (C b).hom ≫ (N b).hom ≫ ω (.retained ⟨j, by omega⟩ b) =
      κ (.retained ⟨j, by omega⟩ b) := by
  simp only [arithmeticFourthAccumulatedLastIso, Iso.trans_hom, Category.assoc]
  rw [arithmeticFourthOuterLast_chart_eq, arithmeticFourthInitialLast_chart_eq,
    arithmeticFourthLast_chart, arithmeticThirdInitialAtlasChart_retained,
    arithmeticThirdLast_chart, arithmeticSecondJointLast_chart]
  have h := arithmeticResidualLiftAtlasCorrection_chart hπ data H m j hj u hu
    (.retained ⟨j, by omega⟩ b)
  simpa only [arithmeticResidualLiftAtlasCorrection, ↓reduceIte] using h

variable (ha : 0 = j)
local notation "J" => arithmeticFourthOuterInitialZeroIdentification hπ data H m j hj u hu ha
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "P" => arithmeticInitialPunctureInclusion π m W (π ^ 1) H.a1_unit H.scale_div
local notation "E" => arithmeticInitialPunctureIso π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "B" => arithmeticRetainedRightParameter data H m j hj
  (Fin.mk 0 (Nat.zero_lt_succ j))

/-- The depth-zero initial overlap meets the full last factor with its original base intact. -/
@[reassoc] theorem arithmeticFourthOuterAtlas_zero_initial (b : Bool) :
    P ≫ (J b).hom ≫ ω (.initial b) = (E).inv ≫ B ≫
      rightBranchOpen Q τ ≫ (O b).hom ≫ (C b).hom ≫ (N b).hom ≫
        ω (.retained ⟨j, by omega⟩ b) := by
  rw [arithmeticFourthAccumulatedLast_chart,
    arithmeticFourthOuterAtlasChart_initial_zero, arithmeticThirdAtlasChart_initial,
    changedArithmeticAtlas_normalized_initial]
  subst j
  rfl

end FLT.Mazur.WeierstrassDividedDepth

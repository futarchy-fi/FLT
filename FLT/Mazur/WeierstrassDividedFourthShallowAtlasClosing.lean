/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthShallowUnchanged
public import FLT.Mazur.WeierstrassDividedFourthOuterAtlasClosing

/-!
# Closing overlaps retained by the fourth depth-two atlas

The new depth-two factors preserve the complete last and terminal charts.
Both closing residuals still cancel on the fourth layer.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthLastOrientedIso arithmeticFourthOuterAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticFourthAtlasObject hπ data H m j hj u hu
local notation "E" => arithmeticFourthAtlasCorrection hπ data H m j hj u hu
local notation "ι" => arithmeticFourthShallowAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticThirdInitialAtlasChart hπ data H m j hj u hu
local notation "C" => arithmeticFourthLastOrientedIso hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "L" => arithmeticClosingRetainedBoundary data H m
local notation "F" => arithmeticFourthTerminalIso hπ data H m j hj u hu
local notation "s" => arithmeticFourthTerminalSmoothing hπ data H j hj u hu m
local notation "N₄" => arithmeticFourthOuterLastIdentification hπ data H m j hj u hu

/-- The last retained label keeps its complete fourth normalized smoothing. -/
def arithmeticFourthShallowLastIdentification (b : Bool) :
    PolygonSmoothing.chart Q τ ≅
      arithmeticFourthShallowAtlasObject hπ data H m j hj u hu (.retained ⟨j, by omega⟩ b) :=
  N₄ b ≪≫ arithmeticFourthShallowUnchangedIdentification hπ data H m j hj u hu
    ⟨j, by omega⟩ (show ¬(j = 2 ∧ j = 0) by omega) b

local notation "N" => arithmeticFourthShallowLastIdentification hπ data H m j hj u hu

/-- The installed last chart retains the same global map. -/
@[reassoc] theorem arithmeticFourthShallowLast_chart_eq (b : Bool) :
    (N b).hom ≫ ι (.retained ⟨j, by omega⟩ b) =
      (N₄ b).hom ≫ arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
        (.retained ⟨j, by omega⟩ b) := by
  rw [arithmeticFourthShallowLastIdentification, Iso.trans_hom, Category.assoc,
    arithmeticFourthShallowUnchanged_chart]

/-- Both installed closing overlaps have the full joint residual, at every arithmetic order. -/
@[reassoc] theorem arithmeticFourthShallowAtlas_residual_closing (b : Bool) :
    (L ≫ (O b).hom) ≫ (N b).hom ≫ ι (.retained ⟨j, by omega⟩ b) =
      (arithmeticFourthClosingResidual hπ data H m j hj u hu b).hom ≫
        punctureOpen s b ≫ ι .terminal := by
  rw [arithmeticFourthShallowLast_chart_eq, arithmeticFourthShallowAtlasChart_terminal]
  exact arithmeticFourthOuterAtlas_residual_closing hπ data H m j hj u hu b

omit m in
/-- At stage four both closing overlaps are the standard complete punctures in this atlas. -/
@[reassoc] theorem arithmeticFourthShallowAtlas_closing_fourth (b : Bool) :
    (arithmeticClosingRetainedBoundary data H 4 ≫
        (twistedRetainedOrientation data H 4 b).hom) ≫
      (arithmeticFourthShallowLastIdentification hπ data H 4 j hj u hu b).hom ≫
        arithmeticFourthShallowAtlasChart hπ data H 4 j hj u hu (.retained ⟨j, by omega⟩ b) =
      punctureOpen (arithmeticFourthTerminalSmoothing hπ data H j hj u hu 4) b ≫
        arithmeticFourthShallowAtlasChart hπ data H 4 j hj u hu .terminal := by
  rw [arithmeticFourthShallowLast_chart_eq, arithmeticFourthShallowAtlasChart_terminal]
  exact arithmeticFourthOuterAtlas_closing_fourth hπ data H j hj u hu b

end FLT.Mazur.WeierstrassDividedDepth

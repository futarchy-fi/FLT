/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthInitialLast
public import FLT.Mazur.WeierstrassDividedFourthAtlasClosing

/-!
# Closing squares preserved by the depth-one initial correction

The last retained label is identified with its unchanged smoothing. The
terminal label keeps the exact fourth rebased smoothing at every order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthLastOrientedIso arithmeticFourthInitialAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticFourthAtlasObject hπ data H m j hj u hu
local notation "E" => arithmeticFourthAtlasCorrection hπ data H m j hj u hu
local notation "ι" => arithmeticFourthInitialAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticThirdInitialAtlasChart hπ data H m j hj u hu
local notation "C" => arithmeticFourthLastOrientedIso hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "L" => arithmeticClosingRetainedBoundary data H m
local notation "F" => arithmeticFourthTerminalIso hπ data H m j hj u hu
local notation "s" => arithmeticFourthTerminalSmoothing hπ data H j hj u hu m
local notation "N" => arithmeticFourthInitialLastIdentification hπ data H m j hj u hu
local notation "M" => arithmeticThirdLastIdentification hπ data H m j hj u hu
local notation "σ" => arithmeticThirdTerminalSmoothing hπ data H j hj u hu m

/-- Both installed closing overlaps have the full joint residual, at every arithmetic order. -/
@[reassoc] theorem arithmeticFourthInitialAtlas_residual_closing (b : Bool) :
    (L ≫ (O b).hom) ≫ (N b).hom ≫ ι (.retained ⟨j, by omega⟩ b) =
      (arithmeticFourthClosingResidual hπ data H m j hj u hu b).hom ≫
        punctureOpen s b ≫ ι .terminal := by
  rw [arithmeticFourthInitialLast_chart_eq, arithmeticFourthInitialAtlasChart_terminal]
  exact arithmeticFourthAtlas_residual_closing hπ data H m j hj u hu b

omit m in
/-- At stage four both closing overlaps are the standard complete punctures in this atlas. -/
@[reassoc] theorem arithmeticFourthInitialAtlas_closing_fourth (b : Bool) :
    (arithmeticClosingRetainedBoundary data H 4 ≫
        (twistedRetainedOrientation data H 4 b).hom) ≫
      (arithmeticFourthInitialLastIdentification hπ data H 4 j hj u hu b).hom ≫
        arithmeticFourthInitialAtlasChart hπ data H 4 j hj u hu (.retained ⟨j, by omega⟩ b) =
      punctureOpen (arithmeticFourthTerminalSmoothing hπ data H j hj u hu 4) b ≫
        arithmeticFourthInitialAtlasChart hπ data H 4 j hj u hu .terminal := by
  rw [arithmeticFourthInitialLast_chart_eq, arithmeticFourthInitialAtlasChart_terminal]
  exact arithmeticFourthAtlas_closing_fourth hπ data H j hj u hu b

end FLT.Mazur.WeierstrassDividedDepth

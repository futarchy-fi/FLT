/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthAtlasIdentification
public import FLT.Mazur.WeierstrassDividedFourthTransitions
public import FLT.Mazur.WeierstrassDividedThirdAtlasClosing

/-!
# Actual closing squares in the installed fourth atlas

The last retained label is identified with its unchanged smoothing. The
terminal label keeps the exact fourth rebased smoothing at every order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthLastOrientedIso arithmeticFourthAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticFourthAtlasObject hπ data H m j hj u hu
local notation "E" => arithmeticFourthAtlasCorrection hπ data H m j hj u hu
local notation "ι" => arithmeticFourthAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticThirdInitialAtlasChart hπ data H m j hj u hu
local notation "C" => arithmeticFourthLastOrientedIso hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "L" => arithmeticClosingRetainedBoundary data H m
local notation "F" => arithmeticFourthTerminalIso hπ data H m j hj u hu
local notation "s" => arithmeticFourthTerminalSmoothing hπ data H j hj u hu m
local notation "N" => arithmeticFourthLastIdentification hπ data H m j hj u hu
local notation "M" => arithmeticThirdLastIdentification hπ data H m j hj u hu
local notation "σ" => arithmeticThirdTerminalSmoothing hπ data H j hj u hu m

/-- Both installed closing overlaps have the full joint residual, at every arithmetic order. -/
@[reassoc] theorem arithmeticFourthAtlas_residual_closing (b : Bool) :
    (L ≫ (O b).hom) ≫ (N b).hom ≫ ι (.retained ⟨j, by omega⟩ b) =
      (arithmeticFourthClosingResidual hπ data H m j hj u hu b).hom ≫
        punctureOpen s b ≫ ι .terminal := by
  have ht := arithmeticFourthAtlasCorrection_chart hπ data H m j hj u hu .terminal
  change (F).hom ≫ ι .terminal = κ .terminal at ht
  apply (cancel_epi (arithmeticFourthLastEdgeIso hπ data H m j hj u hu b true).hom).mp
  calc
    _ = (L ≫ (O b).hom) ≫ (M b).hom ≫ κ (.retained ⟨j, by omega⟩ b) := by
      rw [← Category.assoc _ (L ≫ (O b).hom),
        ← arithmeticFourthLastOrientedIso_closing, Category.assoc, Category.assoc,
        arithmeticFourthLast_chart, Category.assoc]
    _ = (arithmeticThirdClosingResidual hπ data H m j hj u hu b).hom ≫
        punctureOpen σ b ≫ κ .terminal :=
      by simpa only [arithmeticThirdInitialAtlasChart_retained,
        arithmeticThirdInitialAtlasChart_terminal] using
          arithmeticThirdAtlas_residual_closing hπ data H m j hj u hu b
    _ = _ := by
      simp only [arithmeticFourthClosingResidual, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Iso.hom_inv_id_assoc]
      rw [← arithmeticFourthTerminalIso_puncture_assoc, ht]

omit m in
/-- At stage four both closing overlaps are the standard complete punctures in this atlas. -/
@[reassoc] theorem arithmeticFourthAtlas_closing_fourth (b : Bool) :
    (arithmeticClosingRetainedBoundary data H 4 ≫
        (twistedRetainedOrientation data H 4 b).hom) ≫
      (arithmeticFourthLastIdentification hπ data H 4 j hj u hu b).hom ≫
        arithmeticFourthAtlasChart hπ data H 4 j hj u hu (.retained ⟨j, by omega⟩ b) =
      punctureOpen (arithmeticFourthTerminalSmoothing hπ data H j hj u hu 4) b ≫
        arithmeticFourthAtlasChart hπ data H 4 j hj u hu .terminal := by
  have h := arithmeticFourthAtlas_residual_closing hπ data H 4 j hj u hu b
  rw [← arithmeticFourthClosingEquiv_spec, arithmeticFourthClosingEquiv_fourth,
    punctureSpecIso_refl, Iso.refl_hom] at h
  simpa only [branchTorus, Category.id_comp] using h

end FLT.Mazur.WeierstrassDividedDepth

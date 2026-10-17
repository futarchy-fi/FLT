/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdAtlasIdentification
public import FLT.Mazur.WeierstrassDividedThirdTransitions

/-!
# Actual closing squares in the installed third atlas

The last retained label is identified with its unchanged smoothing. The
terminal label keeps the exact third rebased smoothing at every order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticThirdLastOrientedIso arithmeticThirdAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticThirdAtlasObject hπ data H m j hj u hu
local notation "E" => arithmeticThirdAtlasCorrection hπ data H m j hj u hu
local notation "ι" => arithmeticThirdAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticSecondJointAtlasChart hπ data H m j hj u hu
local notation "C" => arithmeticThirdLastOrientedIso hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "L" => arithmeticClosingRetainedBoundary data H m
local notation "F" => arithmeticThirdTerminalIso hπ data H m j hj u hu
local notation "s" => arithmeticThirdTerminalSmoothing hπ data H j hj u hu m
local notation "N" => arithmeticThirdLastIdentification hπ data H m j hj u hu
local notation "M" => arithmeticSecondJointLastIdentification hπ data H m j hj u hu
local notation "σ" => arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu m

/-- Both installed closing overlaps have the full joint residual, at every arithmetic order. -/
@[reassoc] theorem arithmeticThirdAtlas_residual_closing (b : Bool) :
    (L ≫ (O b).hom) ≫ (N b).hom ≫ ι (.retained ⟨j, by omega⟩ b) =
      (arithmeticThirdClosingResidual hπ data H m j hj u hu b).hom ≫
        punctureOpen s b ≫ ι .terminal := by
  have ht := arithmeticThirdAtlasCorrection_chart hπ data H m j hj u hu .terminal
  change (F).hom ≫ ι .terminal = κ .terminal at ht
  apply (cancel_epi (arithmeticThirdLastEdgeIso hπ data H m j hj u hu b true).hom).mp
  calc
    _ = (L ≫ (O b).hom) ≫ (M b).hom ≫ κ (.retained ⟨j, by omega⟩ b) := by
      rw [← Category.assoc _ (L ≫ (O b).hom),
        ← arithmeticThirdLastOrientedIso_closing, Category.assoc, Category.assoc,
        arithmeticThirdLast_chart, Category.assoc]
    _ = (arithmeticSecondJointClosingResidual hπ data H m j hj u hu b).hom ≫
        punctureOpen σ b ≫ κ .terminal :=
      arithmeticSecondJointAtlas_residual_closing hπ data H m j hj u hu b
    _ = _ := by
      simp only [arithmeticThirdClosingResidual, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Iso.hom_inv_id_assoc]
      rw [← arithmeticThirdTerminalIso_puncture_assoc, ht]

omit m in
/-- At stage three both closing overlaps are the standard complete punctures in this atlas. -/
@[reassoc] theorem arithmeticThirdAtlas_closing_third (b : Bool) :
    (arithmeticClosingRetainedBoundary data H 3 ≫
        (twistedRetainedOrientation data H 3 b).hom) ≫
      (arithmeticThirdLastIdentification hπ data H 3 j hj u hu b).hom ≫
        arithmeticThirdAtlasChart hπ data H 3 j hj u hu (.retained ⟨j, by omega⟩ b) =
      punctureOpen (arithmeticThirdTerminalSmoothing hπ data H j hj u hu 3) b ≫
        arithmeticThirdAtlasChart hπ data H 3 j hj u hu .terminal := by
  have h := arithmeticThirdAtlas_residual_closing hπ data H 3 j hj u hu b
  rw [← arithmeticThirdClosingEquiv_spec, arithmeticThirdClosingEquiv_third,
    punctureSpecIso_refl, Iso.refl_hom] at h
  simpa only [branchTorus, Category.id_comp] using h

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInitialPunctureTransport
public import FLT.Mazur.WeierstrassModificationXArithmeticFactorRatioPuncture

/-!
# The exact full initial factor-ratio boundary after all node corrections

The old Mobius coordinate and the corrected squared-factor coordinate differ
by an explicit Laurent automorphism. Transport keeps that automorphism intact.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "N" => arithmeticInitialFactorRatioChart π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "s" => PolygonArithmeticSimultaneous.State.initial D m

local notation "E" => arithmeticZeroDiagonalInitialOpenIso hπ data H m hj u hu
local notation "T" => arithmeticZeroDiagonalInitialTotalNodeIso hπ data H m hj u hu
local notation "A" => arithmeticZeroFiniteInitialTotalPunctureIso hπ data H m hj u hu m
local notation "P" => arithmeticInitialPunctureInclusion π m W (π ^ 1) H.a1_unit H.scale_div
local notation "J" => arithmeticInitialNormalizedPunctureIso π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "M" => arithmeticInitialMobiusParameter π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "L" => arithmeticFactorRatioLaurentIso π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "P₀" => arithmeticZeroFiniteInitialPuncture hπ data H m m 0 hj u hu
local notation "F" => arithmeticZeroDiagonalInitialFactorRatio hπ data H m hj u hu

/-- The full original D(p) has the explicit accumulated Mobius and node parameter. -/
@[reassoc] theorem arithmeticZeroDiagonalInitialOpenIso_puncture (b : Bool) :
    P ≫ (E b).hom = (J).hom ≫ (A b true).hom ≫ P₀ b := by
  apply (cancel_mono
    (arithmeticZeroFiniteInitialNodeChart hπ data H m m 0 hj u hu b)).mp
  simp only [Category.assoc, arithmeticZeroFiniteInitialPuncture_nodeChart]
  rw [arithmeticZeroDiagonalInitialOpenIso,
    arithmeticZeroFiniteAtlasIso_initial_nodeChart,
    arithmeticInitialNormalizedPunctureIso_boundary_assoc π m W (π ^ 1)
      (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _)]
  have h := arithmeticZeroFiniteInitialTotalNodeIso_puncture hπ data H m hj u hu m b true
  simpa only [punctureOpen_true, Category.assoc] using congrArg ((J).hom ≫ ·) h

/-- The exact boundary change from the original Mobius chart to the full factor ratio. -/
def arithmeticZeroDiagonalFactorRatioBoundaryIso (b : Bool) :
    branchTorus Q ≅ branchTorus Q :=
  (A b true).symm ≪≫ (M).symm ≪≫ L ≪≫ A b true

local notation "B" => arithmeticZeroDiagonalFactorRatioBoundaryIso hπ data H m hj u hu

/-- The entire initial puncture keeps the conjugated, unreduced Laurent correction. -/
@[reassoc] theorem arithmeticZeroDiagonalInitialFactorRatio_puncture (b : Bool) :
    P₀ b ≫ F b = (B b).hom ≫ leftBranchOpen Q (s b) := by
  apply (cancel_epi ((J).hom ≫ (A b true).hom)).mp
  rw [← Category.assoc, Category.assoc (J).hom (A b true).hom (P₀ b),
    ← arithmeticZeroDiagonalInitialOpenIso_puncture]
  simp only [Category.assoc, arithmeticZeroDiagonalInitialFactorRatio_transport]
  have hP : P ≫ N = (J).hom ≫ (M).inv ≫ (L).hom ≫ leftBranchOpen Q τ := by
    rw [← arithmeticInitialNormalizedPunctureIso_inv_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← arithmeticFactorRatioLaurentIso_boundary,
      arithmeticInitialPunctureIso_inv_boundary_assoc]
  rw [← Category.assoc P N, hP]
  simp only [arithmeticZeroDiagonalFactorRatioBoundaryIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  have ht := arithmeticZeroDiagonalInitialTotalNodeIso_puncture hπ data H m hj u hu b true
  simpa only [punctureOpen_true, Category.assoc] using
    congrArg ((J).hom ≫ (M).inv ≫ (L).hom ≫ ·) ht

end FLT.Mazur.WeierstrassDividedDepth

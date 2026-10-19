/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInitialPunctureTransport
public import FLT.Mazur.WeierstrassDividedOneDiagonalFactorRatio
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
  arithmeticOneFiniteInitialIso arithmeticInitialFactorRatioChart
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "N" => arithmeticInitialFactorRatioChart π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "D" => arithmeticOneDiagonalState hπ data H hj u hu
local notation "s" => PolygonArithmeticRetainedChain.State.initial D m

local notation "E" => arithmeticOneDiagonalInitialTotalOpenIso hπ data H m hj u hu
local notation "T" => arithmeticOneDiagonalInitialTotalNodeIso hπ data H m hj u hu
local notation "A" => arithmeticOneFiniteInitialTotalPunctureIso hπ data H m hj u hu m
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
local notation "P₀" => arithmeticOneFiniteInitialPuncture hπ data H m m hj u hu
local notation "F" => arithmeticOneDiagonalInitialFactorRatio hπ data H m hj u hu

/-- The full original D(p) has the explicit accumulated Mobius and node parameter. -/
@[reassoc] theorem arithmeticOneDiagonalInitialTotalOpenIso_puncture (b : Bool) :
    P ≫ (E b).hom = (J).hom ≫ (A b true).hom ≫ P₀ b := by
  apply (cancel_mono
    (arithmeticOneFiniteInitialNodeChart hπ data H m m hj u hu b)).mp
  simp only [Category.assoc, arithmeticOneFiniteInitialPuncture_nodeChart]
  rw [arithmeticOneDiagonalInitialTotalOpenIso_nodeChart,
    arithmeticInitialNormalizedPunctureIso_boundary_assoc π m W (π ^ 1)
      (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _)]
  have h := arithmeticOneFiniteInitialTotalNodeIso_puncture hπ data H m hj u hu m b true
  simpa only [punctureOpen_true, Category.assoc,
    arithmeticOneDiagonalInitialTotalNodeIso] using congrArg ((J).hom ≫ ·) h

/-- The exact boundary change from the original Mobius chart to the full factor ratio. -/
def arithmeticOneDiagonalFactorRatioBoundaryIso (b : Bool) :
    branchTorus Q ≅ branchTorus Q :=
  (A b true).symm ≪≫ (M).symm ≪≫ L ≪≫ A b true

local notation "B" => arithmeticOneDiagonalFactorRatioBoundaryIso hπ data H m hj u hu

/-- The entire initial puncture keeps the conjugated, unreduced Laurent correction. -/
@[reassoc] theorem arithmeticOneDiagonalInitialFactorRatio_puncture (b : Bool) :
    P₀ b ≫ F b = (B b).hom ≫ leftBranchOpen Q (s b) := by
  apply (cancel_epi ((J).hom ≫ (A b true).hom)).mp
  rw [← Category.assoc, Category.assoc (J).hom (A b true).hom (P₀ b),
    ← arithmeticOneDiagonalInitialTotalOpenIso_puncture]
  simp only [Category.assoc, arithmeticOneDiagonalInitialFactorRatio_transport]
  have hP : P ≫ N = (J).hom ≫ (M).inv ≫ (L).hom ≫ leftBranchOpen Q τ := by
    rw [← arithmeticInitialNormalizedPunctureIso_inv_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← arithmeticFactorRatioLaurentIso_boundary,
      arithmeticInitialPunctureIso_inv_boundary_assoc]
  rw [← Category.assoc P N, hP]
  simp only [arithmeticOneDiagonalFactorRatioBoundaryIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  have ht := arithmeticOneDiagonalInitialTotalNodeIso_puncture hπ data H m hj u hu b true
  simpa only [punctureOpen_true, Category.assoc] using
    congrArg ((J).hom ≫ (M).inv ≫ (L).hom ≫ ·) ht

end FLT.Mazur.WeierstrassDividedDepth

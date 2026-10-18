/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedFullUnion

/-!
# The unreduced retained boundary after whole-node infinity normalization

The initial/infinity equations are now solved on the full source union.
The exact remaining retained-side correction still contains the complete
Mobius and squared-factor Laurent substitutions and all accumulated factors.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticZeroFiniteAtlasIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "N" => arithmeticInitialFactorRatioChart π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "P" => arithmeticFactorRatioOverlapParameter π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "E" => arithmeticZeroDiagonalInitialOpenIso hπ data H m hj u hu
local notation "T" => arithmeticZeroDiagonalInitialTotalNodeIso hπ data H m hj u hu
local notation "F" => arithmeticZeroDiagonalInitialFactorRatio hπ data H m hj u hu
local notation "l" => arithmeticZeroDiagonalInitialOverlap hπ data H m hj u hu
local notation "i" => arithmeticZeroDiagonalOverlapToInfinity hπ data H m hj u hu
local notation "V" => arithmeticZeroDiagonalInfinityParameterIso hπ data H m hj u hu
local notation "A" => arithmeticZeroFiniteAtlasObject hπ data H m m hj u hu

local notation "f" => arithmeticZeroInfinityNormalizedInitial hπ data H m hj u hu
local notation "A₀" => arithmeticZeroFiniteInitialTotalPunctureIso hπ data H m hj u hu m
local notation "P₀" => arithmeticZeroFiniteInitialPuncture hπ data H m m 0 hj u hu
local notation "M" => arithmeticInitialMobiusParameter π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "L" => arithmeticFactorRatioLaurentIso π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "s" => PolygonArithmeticSimultaneous.State.initial D m

/-- The remaining full retained parameter after undoing the whole initial node transport. -/
def arithmeticZeroInfinityNormalizedRetainedParameter (b : Bool) :
    branchTorus Q ≅ branchTorus Q := (A₀ b true).symm ≪≫ (M).symm ≪≫ L

local notation "K" => arithmeticZeroInfinityNormalizedRetainedParameter hπ data H m hj u hu

omit [IsBezout R] in
/-- Undoing the full node correction undoes its entire left-boundary substitution. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedNode_left (b : Bool) :
    leftBranchOpen Q (s b) ≫ (T b).inv = (A₀ b true).inv ≫ leftBranchOpen Q τ := by
  apply (cancel_epi (A₀ b true).hom).mp
  rw [Iso.hom_inv_id_assoc]
  have h := arithmeticZeroDiagonalInitialTotalNodeIso_puncture hπ data H m hj u hu b true
  rw [punctureOpen_true, punctureOpen_true] at h
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The original full D(p) retains its exact unreduced Laurent correction on the whole node. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedInitial_retained (b : Bool) :
    P₀ b ≫ f b = (K b).hom ≫ leftBranchOpen Q τ := by
  rw [arithmeticZeroInfinityNormalizedInitial, ← Category.assoc,
    arithmeticZeroDiagonalInitialFactorRatio_puncture, Category.assoc,
    arithmeticZeroInfinityNormalizedNode_left]
  simp only [arithmeticZeroDiagonalFactorRatioBoundaryIso,
    arithmeticZeroInfinityNormalizedRetainedParameter, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]

omit [IsBezout R] in
/-- The complete remaining parameter has its explicit inverse, without coefficient reduction. -/
theorem arithmeticZeroInfinityNormalizedRetainedParameter_inv (b : Bool) :
    (K b).inv = (L).inv ≫ (M).hom ≫ (A₀ b true).hom := by
  simp only [arithmeticZeroInfinityNormalizedRetainedParameter, Iso.trans_inv,
    Iso.symm_inv, Category.assoc]

/-- Any prescribed full retained attachment agrees precisely when its Laurent parameters agree. -/
theorem arithmeticZeroInfinityNormalizedInitial_retained_iff (b : Bool)
    (q : branchTorus Q ⟶ branchTorus Q) :
    P₀ b ≫ f b = q ≫ leftBranchOpen Q τ ↔ (K b).hom = q := by
  rw [arithmeticZeroInfinityNormalizedInitial_retained]
  exact cancel_mono (leftBranchOpen Q τ)

end FLT.Mazur.WeierstrassDividedDepth

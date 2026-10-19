/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInfinityNormalizedFullUnion
public import FLT.Mazur.WeierstrassDividedOneDiagonalFactorRatioBoundary

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
  arithmeticOneFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticOneFiniteAtlasIso
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "N" => arithmeticInitialFactorRatioChart π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "P" => arithmeticFactorRatioOverlapParameter π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "E" => arithmeticOneDiagonalInitialTotalOpenIso hπ data H m hj u hu
local notation "T" => arithmeticOneDiagonalInitialTotalNodeIso hπ data H m hj u hu
local notation "F" => arithmeticOneDiagonalInitialFactorRatio hπ data H m hj u hu
local notation "l" => arithmeticOneDiagonalInitialOverlap hπ data H m hj u hu
local notation "i" => arithmeticOneDiagonalOverlapToInfinity hπ data H m hj u hu
local notation "V" => arithmeticOneDiagonalInfinityParameterIso hπ data H m hj u hu
local notation "A" => arithmeticOneFiniteAtlasObject hπ data H m m hj u hu

local notation "f" => arithmeticOneInfinityNormalizedInitial hπ data H m hj u hu
local notation "A₀" => arithmeticOneFiniteInitialTotalPunctureIso hπ data H m hj u hu m
local notation "P₀" => arithmeticOneFiniteInitialPuncture hπ data H m m hj u hu
local notation "M" => arithmeticInitialMobiusParameter π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "L" => arithmeticFactorRatioLaurentIso π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "D" => arithmeticOneDiagonalState hπ data H hj u hu
local notation "s" => PolygonArithmeticRetainedChain.State.initial D m

/-- The remaining full retained parameter after undoing the whole initial node transport. -/
def arithmeticOneInfinityNormalizedRetainedParameter (b : Bool) :
    branchTorus Q ≅ branchTorus Q := (A₀ b true).symm ≪≫ (M).symm ≪≫ L

local notation "K" => arithmeticOneInfinityNormalizedRetainedParameter hπ data H m hj u hu

/-- Undoing the full node correction undoes its entire left-boundary substitution. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedNode_left (b : Bool) :
    leftBranchOpen Q (s b) ≫ (T b).inv = (A₀ b true).inv ≫ leftBranchOpen Q τ := by
  apply (cancel_epi (A₀ b true).hom).mp
  rw [Iso.hom_inv_id_assoc]
  have h := arithmeticOneDiagonalInitialTotalNodeIso_puncture hπ data H m hj u hu b true
  rw [punctureOpen_true, punctureOpen_true] at h
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The original full D(p) retains its exact unreduced Laurent correction on the whole node. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedInitial_retained (b : Bool) :
    P₀ b ≫ f b = (K b).hom ≫ leftBranchOpen Q τ := by
  rw [arithmeticOneInfinityNormalizedInitial, ← Category.assoc,
    arithmeticOneDiagonalInitialFactorRatio_puncture, Category.assoc,
    arithmeticOneInfinityNormalizedNode_left]
  simp only [arithmeticOneDiagonalFactorRatioBoundaryIso,
    arithmeticOneInfinityNormalizedRetainedParameter, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]

/-- The complete remaining parameter has its explicit inverse, without coefficient reduction. -/
theorem arithmeticOneInfinityNormalizedRetainedParameter_inv (b : Bool) :
    (K b).inv = (L).inv ≫ (M).hom ≫ (A₀ b true).hom := by
  simp only [arithmeticOneInfinityNormalizedRetainedParameter, Iso.trans_inv,
    Iso.symm_inv, Category.assoc]

/-- Any prescribed full retained attachment agrees precisely when its Laurent parameters agree. -/
theorem arithmeticOneInfinityNormalizedInitial_retained_iff (b : Bool)
    (q : branchTorus Q ⟶ branchTorus Q) :
    P₀ b ≫ f b = q ≫ leftBranchOpen Q τ ↔ (K b).hom = q := by
  rw [arithmeticOneInfinityNormalizedInitial_retained]
  exact cancel_mono (leftBranchOpen Q τ)

end FLT.Mazur.WeierstrassDividedDepth

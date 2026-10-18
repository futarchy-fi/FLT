/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedRetainedGluing

/-!
# The exact retained attachment preserves the original coefficient base

Both the independent attached target and its complete source-union comparison
lie over the original arithmetic quotient ring.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteAtlasIso simultaneousTwistedArithmeticIso
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "s" => PolygonArithmeticSimultaneous.State.last D m
local notation "w" => arithmeticZeroInfinityNormalizedRetainedToUnion hπ data H m hj u hu
local notation "r" => arithmeticZeroInfinityNormalizedRetainedSide hπ data H m hj u hu
local notation "v" => arithmeticZeroInfinityNormalizedTargetLeft data H m
local notation "F" => arithmeticZeroInfinityNormalizedFullComparison hπ data H m hj u hu
local notation "G" => arithmeticZeroInfinityNormalizedRetainedPushoutIso hπ data H m hj u hu
local notation "g" => arithmeticZeroInfinityNormalizedRetainedToGlobal hπ data H m hj u hu
local notation "V" => arithmeticZeroInfinityNormalizedRetainedUnion hπ data H m hj u hu
local notation "J" => arithmeticZeroInfinityNormalizedRetainedUnionIso hπ data H m hj u hu
local notation "B" => arithmeticZeroDiagonalSourceToBase hπ data H m hj u hu
local notation "p" => arithmeticZeroInfinityNormalizedTargetToBase data H m

/-- The entire independent retained attachment has its original quotient coefficient projection. -/
def arithmeticZeroInfinityNormalizedRetainedTargetToBase (b : Bool) :
    arithmeticZeroInfinityNormalizedRetainedTarget hπ data H m hj u hu b ⟶ Spec (.of Q) :=
  pushout.desc p (chartStructure Q (s b)) (by
    rw [arithmeticZeroInfinityNormalizedTargetLeft_base,
      arithmeticZeroInfinityNormalizedRetainedSide_base])

local notation "t" => arithmeticZeroInfinityNormalizedRetainedTargetToBase hπ data H m hj u hu

/-- The entire normalized pair retains its original base after attaching the retained node. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedTargetToBase_pair (b : Bool) :
    pushout.inl (v b) (r b) ≫ t b = p := pushout.inl_desc _ _ _

/-- The entire original retained node retains its original base after attachment. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedTargetToBase_retained (b : Bool) :
    pushout.inr (v b) (r b) ≫ t b = chartStructure Q (s b) := pushout.inr_desc _ _ _

/-- The full pushout comparison preserves the actual original global coefficient projection. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPushoutIso_base (b : Bool) :
    (G b).hom ≫ t b = g b ≫ B := by
  apply pushout.hom_ext
  · rw [arithmeticZeroInfinityNormalizedRetainedPushoutIso_pair_assoc,
      arithmeticZeroInfinityNormalizedRetainedTargetToBase_pair,
      arithmeticZeroInfinityNormalizedFullComparison_base,
      arithmeticZeroInfinityNormalizedRetainedToGlobal_pair_assoc]
  · rw [arithmeticZeroInfinityNormalizedRetainedPushoutIso_retained_assoc,
      arithmeticZeroInfinityNormalizedRetainedTargetToBase_retained,
      arithmeticZeroInfinityNormalizedRetainedToGlobal_retained_assoc,
      arithmeticZeroDiagonalAtlas_retained_base]

/-- The independent target comparison of the whole actual union is over the original base. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedComparison_base (b : Bool) :
    (arithmeticZeroInfinityNormalizedRetainedComparison hπ data H m hj u hu b).hom ≫ t b =
      (V b).ι ≫ B := by
  apply (cancel_epi (J b).hom).mp
  simp only [arithmeticZeroInfinityNormalizedRetainedComparison, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc, arithmeticZeroInfinityNormalizedRetainedPushoutIso_base,
    arithmeticZeroInfinityNormalizedRetainedUnionIso_global_assoc]

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInfinityNormalizedRetainedGluing
public import FLT.Mazur.WeierstrassDividedOneRetainedAtlasBase
public import FLT.Mazur.WeierstrassDividedOneRetainedCoefficientRestriction

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
  arithmeticOneFiniteAtlasIso simultaneousTwistedArithmeticIso
  arithmeticOneFiniteInitialIso arithmeticInitialFactorRatioChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "D" => arithmeticOneDiagonalState hπ data H hj u hu
local notation "s" => fun b ↦ PolygonArithmeticRetainedChain.State.retained D m 0 b
local notation "w" => arithmeticOneInfinityNormalizedRetainedToUnion hπ data H m hj u hu
local notation "r" => arithmeticOneInfinityNormalizedRetainedSide hπ data H m hj u hu
local notation "v" => arithmeticOneInfinityNormalizedTargetLeft data H m
local notation "F" => arithmeticOneInfinityNormalizedFullComparison hπ data H m hj u hu
local notation "G" => arithmeticOneInfinityNormalizedRetainedPushoutIso hπ data H m hj u hu
local notation "g" => arithmeticOneInfinityNormalizedRetainedToGlobal hπ data H m hj u hu
local notation "V" => arithmeticOneInfinityNormalizedRetainedUnion hπ data H m hj u hu
local notation "J" => arithmeticOneInfinityNormalizedRetainedUnionIso hπ data H m hj u hu
local notation "B" => arithmeticOneDiagonalSourceToBase hπ data H m hj u hu
local notation "p" => arithmeticOneInfinityNormalizedTargetToBase data H m

/-- The entire independent retained attachment has its original quotient coefficient projection. -/
def arithmeticOneInfinityNormalizedRetainedTargetToBase (b : Bool) :
    arithmeticOneInfinityNormalizedRetainedTarget hπ data H m hj u hu b ⟶ Spec (.of Q) :=
  pushout.desc p (chartStructure Q (s b)) (by
    rw [arithmeticOneInfinityNormalizedTargetLeft_base,
      arithmeticOneInfinityNormalizedRetainedSide_base])

local notation "t" => arithmeticOneInfinityNormalizedRetainedTargetToBase hπ data H m hj u hu

omit [IsBezout R] in
/-- The entire normalized pair retains its original base after attaching the retained node. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedRetainedTargetToBase_pair (b : Bool) :
    pushout.inl (v b) (r b) ≫ t b = p := pushout.inl_desc _ _ _

omit [IsBezout R] in
/-- The entire original retained node retains its original base after attachment. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedRetainedTargetToBase_retained (b : Bool) :
    pushout.inr (v b) (r b) ≫ t b = chartStructure Q (s b) := pushout.inr_desc _ _ _

/-- The full pushout comparison preserves the actual original global coefficient projection. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedRetainedPushoutIso_base (b : Bool) :
    (G b).hom ≫ t b = g b ≫ B := by
  apply pushout.hom_ext
  · rw [arithmeticOneInfinityNormalizedRetainedPushoutIso_pair_assoc,
      arithmeticOneInfinityNormalizedRetainedTargetToBase_pair,
      arithmeticOneInfinityNormalizedFullComparison_base,
      arithmeticOneInfinityNormalizedRetainedToGlobal_pair_assoc]
  · rw [arithmeticOneInfinityNormalizedRetainedPushoutIso_retained_assoc,
      arithmeticOneInfinityNormalizedRetainedTargetToBase_retained,
      arithmeticOneInfinityNormalizedRetainedToGlobal_retained_assoc]
    exact (arithmeticOneDiagonalAtlas_retainedFirst_base hπ data H m hj u hu b).symm

/-- The independent target comparison of the whole actual union is over the original base. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedRetainedComparison_base (b : Bool) :
    (arithmeticOneInfinityNormalizedRetainedComparison hπ data H m hj u hu b).hom ≫ t b =
      (V b).ι ≫ B := by
  apply (cancel_epi (J b).hom).mp
  simp only [arithmeticOneInfinityNormalizedRetainedComparison, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc, arithmeticOneInfinityNormalizedRetainedPushoutIso_base,
    arithmeticOneInfinityNormalizedRetainedUnionIso_global_assoc]

end FLT.Mazur.WeierstrassDividedDepth

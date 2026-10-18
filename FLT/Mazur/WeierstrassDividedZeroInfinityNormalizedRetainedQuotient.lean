/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedRetainedBase

/-!
# Original arithmetic quotients on the full retained attachment

Glue the original pair quotient to the actual corrected retained-node quotient.
The comparison respects both full charts and the original global arrow.
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
  arithmeticZeroDiagonalAtlasChart simultaneousTwistedArithmeticRestriction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "w" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedToUnion hπ data H k hj u hu
local notation "r" => fun k ↦ arithmeticZeroInfinityNormalizedRetainedSide hπ data H k hj u hu
local notation "v" => fun k ↦ arithmeticZeroInfinityNormalizedTargetLeft data H k
local notation "F" => fun k ↦ arithmeticZeroInfinityNormalizedFullComparison hπ data H k hj u hu
local notation "G" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedPushoutIso hπ data H k hj u hu
local notation "g" => fun k ↦ arithmeticZeroInfinityNormalizedRetainedToGlobal hπ data H k hj u hu
local notation "U" => fun k ↦ arithmeticZeroInfinityNormalizedFullUnion hπ data H k hj u hu
local notation "c" => fun k ↦ arithmeticZeroDiagonalAtlasChart hπ data H k hj u hu
local notation "S" => arithmeticZeroDiagonalAtlasRestriction hπ data H hj u hu m
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H m 0 hj u hu
local notation "ρ" => closingOverlapRestriction (R := R) (π := π) m
local notation "p" => arithmeticZeroInfinityNormalizedTargetRestriction data H m
local notation "a" => arithmeticZeroInfinityNormalizedFullUnionRestriction hπ data H m hj u hu

/-- Glue the actual corrected retained quotient to the independent full pair quotient. -/
def arithmeticZeroInfinityNormalizedRetainedTargetRestriction (b : Bool) :
    arithmeticZeroInfinityNormalizedRetainedTarget hπ data H m hj u hu b ⟶
      arithmeticZeroInfinityNormalizedRetainedTarget hπ data H (m + 1) hj u hu b :=
  pushout.map (v m b) (r m b) (v (m + 1) b) (r (m + 1) b)
    p (S (.retained ⟨0, by omega⟩ b)) ρ
    (arithmeticZeroInfinityNormalizedTargetLeft_restriction data H m b)
    (arithmeticZeroInfinityNormalizedRetainedSide_restriction hπ data H m hj u hu b)

local notation "t" => arithmeticZeroInfinityNormalizedRetainedTargetRestriction hπ data H m hj u hu

/-- The attached target quotient restricts to the complete original pair quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedTargetRestriction_pair (b : Bool) :
    pushout.inl (v m b) (r m b) ≫ t b = p ≫ pushout.inl (v (m + 1) b) (r (m + 1) b) :=
  pushout.inl_desc _ _ _

/-- The attached target quotient restricts to the actual corrected whole retained-node quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedTargetRestriction_retained (b : Bool) :
    pushout.inr (v m b) (r m b) ≫ t b =
      S (.retained ⟨0, by omega⟩ b) ≫ pushout.inr (v (m + 1) b) (r (m + 1) b) :=
  pushout.inr_desc _ _ _

/-- Transport the full attached quotient through the constructed entire comparison. -/
def arithmeticZeroInfinityNormalizedRetainedPushoutRestriction (b : Bool) :
    pushout (w m b) (r m b) ⟶ pushout (w (m + 1) b) (r (m + 1) b) :=
  (G m b).hom ≫ t b ≫ (G (m + 1) b).inv

local notation "d" =>
  arithmeticZeroInfinityNormalizedRetainedPushoutRestriction hπ data H m hj u hu

/-- The entire attached comparison follows the full target quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPushoutRestriction_comparison
    (b : Bool) :
    d b ≫ (G (m + 1) b).hom = (G m b).hom ≫ t b := by
  simp only [arithmeticZeroInfinityNormalizedRetainedPushoutRestriction, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The source attached quotient restricts to the actual full original pair quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPushoutRestriction_pair (b : Bool) :
    pushout.inl (w m b) (r m b) ≫ d b = a ≫ pushout.inl (w (m + 1) b) (r (m + 1) b) := by
  apply (cancel_mono (G (m + 1) b).hom).mp
  rw [Category.assoc, arithmeticZeroInfinityNormalizedRetainedPushoutRestriction_comparison,
    arithmeticZeroInfinityNormalizedRetainedPushoutIso_pair_assoc, Category.assoc,
    arithmeticZeroInfinityNormalizedRetainedPushoutIso_pair,
    arithmeticZeroInfinityNormalizedRetainedTargetRestriction_pair,
    arithmeticZeroInfinityNormalizedFullComparison_restriction_assoc]

/-- The source attached quotient keeps the entire actual retained-node coefficient arrow. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPushoutRestriction_retained (b : Bool) :
    pushout.inr (w m b) (r m b) ≫ d b =
      S (.retained ⟨0, by omega⟩ b) ≫ pushout.inr (w (m + 1) b) (r (m + 1) b) := by
  apply (cancel_mono (G (m + 1) b).hom).mp
  rw [Category.assoc, arithmeticZeroInfinityNormalizedRetainedPushoutRestriction_comparison,
    arithmeticZeroInfinityNormalizedRetainedPushoutIso_retained_assoc, Category.assoc,
    arithmeticZeroInfinityNormalizedRetainedPushoutIso_retained,
    arithmeticZeroInfinityNormalizedRetainedTargetRestriction_retained]

/-- The entire attached source quotient is the original global quotient on its full image. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPushoutRestriction_global (b : Bool) :
    d b ≫ g (m + 1) b = g m b ≫ q := by
  apply pushout.hom_ext
  · rw [arithmeticZeroInfinityNormalizedRetainedPushoutRestriction_pair_assoc,
      arithmeticZeroInfinityNormalizedRetainedToGlobal_pair,
      arithmeticZeroInfinityNormalizedRetainedToGlobal_pair_assoc,
      arithmeticZeroInfinityNormalizedFullUnionRestriction_global]
  · rw [arithmeticZeroInfinityNormalizedRetainedPushoutRestriction_retained_assoc,
      arithmeticZeroInfinityNormalizedRetainedToGlobal_retained,
      arithmeticZeroInfinityNormalizedRetainedToGlobal_retained_assoc]
    exact arithmeticZeroDiagonalAtlasChart_restriction hπ data H hj u hu m _

end FLT.Mazur.WeierstrassDividedDepth

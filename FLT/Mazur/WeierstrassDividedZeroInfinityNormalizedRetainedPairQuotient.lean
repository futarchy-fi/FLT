/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedRetainedPair

/-!
# Original quotient maps on both complete retained attachments

The two full four-chart quotient maps agree on the common full pair. Their
pushout gives the five-chart quotient, compatible with the original global map.
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
local notation "a" => fun k b ↦ pushout.inl (w k b) (r k b)
local notation "t" => fun k b ↦ pushout.inl (v k b) (r k b)
local notation "G" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedPushoutIso hπ data H k hj u hu
local notation "E" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedPairIso hπ data H k hj u hu
local notation "j" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedPairToGlobal hπ data H k hj u hu
local notation "d" =>
  arithmeticZeroInfinityNormalizedRetainedPushoutRestriction hπ data H m hj u hu
local notation "s" => arithmeticZeroInfinityNormalizedRetainedTargetRestriction hπ data H m hj u hu
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H m 0 hj u hu

/-- Glue the two full source quotients along their original common pair quotient. -/
def arithmeticZeroInfinityNormalizedRetainedPairPushoutRestriction :
    pushout (a m false) (a m true) ⟶ pushout (a (m + 1) false) (a (m + 1) true) :=
  pushout.map (a m false) (a m true) (a (m + 1) false) (a (m + 1) true)
    (d false) (d true)
    (arithmeticZeroInfinityNormalizedFullUnionRestriction hπ data H m hj u hu)
    (arithmeticZeroInfinityNormalizedRetainedPushoutRestriction_pair hπ data H m hj u hu false)
    (arithmeticZeroInfinityNormalizedRetainedPushoutRestriction_pair hπ data H m hj u hu true)

/-- Glue the independently constructed attached quotients along their complete common pair. -/
def arithmeticZeroInfinityNormalizedRetainedPairTargetRestriction :
    arithmeticZeroInfinityNormalizedRetainedPairTarget hπ data H m hj u hu ⟶
      arithmeticZeroInfinityNormalizedRetainedPairTarget hπ data H (m + 1) hj u hu :=
  pushout.map (t m false) (t m true) (t (m + 1) false) (t (m + 1) true)
    (s false) (s true) (arithmeticZeroInfinityNormalizedTargetRestriction data H m)
    (arithmeticZeroInfinityNormalizedRetainedTargetRestriction_pair hπ data H m hj u hu false)
    (arithmeticZeroInfinityNormalizedRetainedTargetRestriction_pair hπ data H m hj u hu true)

local notation "d₂" =>
  arithmeticZeroInfinityNormalizedRetainedPairPushoutRestriction hπ data H m hj u hu
local notation "s₂" =>
  arithmeticZeroInfinityNormalizedRetainedPairTargetRestriction hπ data H m hj u hu

/-- The full source quotient restricts to the first original attachment quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPairPushoutRestriction_first :
    pushout.inl (a m false) (a m true) ≫ d₂ =
      d false ≫ pushout.inl (a (m + 1) false) (a (m + 1) true) := pushout.inl_desc _ _ _

/-- The full source quotient restricts to the opposite original attachment quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPairPushoutRestriction_opposite :
    pushout.inr (a m false) (a m true) ≫ d₂ =
      d true ≫ pushout.inr (a (m + 1) false) (a (m + 1) true) := pushout.inr_desc _ _ _

/-- The full target quotient restricts to the first independent attachment quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPairTargetRestriction_first :
    pushout.inl (t m false) (t m true) ≫ s₂ =
      s false ≫ pushout.inl (t (m + 1) false) (t (m + 1) true) := pushout.inl_desc _ _ _

/-- The full target quotient restricts to the opposite independent attachment quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPairTargetRestriction_opposite :
    pushout.inr (t m false) (t m true) ≫ s₂ =
      s true ≫ pushout.inr (t (m + 1) false) (t (m + 1) true) := pushout.inr_desc _ _ _

/-- The complete five-chart comparison respects both original quotient squares. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPairPushoutRestriction_comparison :
    d₂ ≫ (E (m + 1)).hom = (E m).hom ≫ s₂ := by
  apply pushout.hom_ext
  · rw [arithmeticZeroInfinityNormalizedRetainedPairPushoutRestriction_first_assoc,
      arithmeticZeroInfinityNormalizedRetainedPairIso_first,
      arithmeticZeroInfinityNormalizedRetainedPairIso_first_assoc,
      arithmeticZeroInfinityNormalizedRetainedPairTargetRestriction_first,
      arithmeticZeroInfinityNormalizedRetainedPushoutRestriction_comparison_assoc]
  · rw [arithmeticZeroInfinityNormalizedRetainedPairPushoutRestriction_opposite_assoc,
      arithmeticZeroInfinityNormalizedRetainedPairIso_opposite,
      arithmeticZeroInfinityNormalizedRetainedPairIso_opposite_assoc,
      arithmeticZeroInfinityNormalizedRetainedPairTargetRestriction_opposite,
      arithmeticZeroInfinityNormalizedRetainedPushoutRestriction_comparison_assoc]

/-- The five-chart source quotient is the original global quotient on its entire image. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPairPushoutRestriction_global :
    d₂ ≫ j (m + 1) = j m ≫ q := by
  apply pushout.hom_ext
  · rw [arithmeticZeroInfinityNormalizedRetainedPairPushoutRestriction_first_assoc,
      arithmeticZeroInfinityNormalizedRetainedPairToGlobal_first,
      arithmeticZeroInfinityNormalizedRetainedPairToGlobal_first_assoc,
      arithmeticZeroInfinityNormalizedRetainedPushoutRestriction_global]
  · rw [arithmeticZeroInfinityNormalizedRetainedPairPushoutRestriction_opposite_assoc,
      arithmeticZeroInfinityNormalizedRetainedPairToGlobal_opposite,
      arithmeticZeroInfinityNormalizedRetainedPairToGlobal_opposite_assoc,
      arithmeticZeroInfinityNormalizedRetainedPushoutRestriction_global]

end FLT.Mazur.WeierstrassDividedDepth

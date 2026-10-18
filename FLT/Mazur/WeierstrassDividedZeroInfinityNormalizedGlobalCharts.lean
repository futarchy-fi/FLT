/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedGlobalSystem

/-!
# Original full chart equations in the global exact-twist target

The full original retained nodes and common terminal keep both closing
equations. The complete normalized initial/infinity pair has a single target
inclusion, shared by both retained attachments.
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
  arithmeticZeroDiagonalAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "s" => PolygonArithmeticSimultaneous.State.last D m
local notation "t" => PolygonArithmeticSimultaneous.State.terminal D m
local notation "c" => arithmeticZeroDiagonalAtlasChart hπ data H m hj u hu
local notation "j" => arithmeticZeroInfinityNormalizedRetainedPairToGlobal hπ data H m hj u hu
local notation "k" => arithmeticZeroInfinityNormalizedRetainedPairTargetChart hπ data H m hj u hu
local notation "v" => arithmeticZeroInfinityNormalizedTargetLeft data H m
local notation "w" => arithmeticZeroInfinityNormalizedRetainedToUnion hπ data H m hj u hu
local notation "r₀" => arithmeticZeroInfinityNormalizedRetainedSide hπ data H m hj u hu
local notation "a₀" => fun b ↦ pushout.inl (w b) (r₀ b)
local notation "b₀" => fun b ↦ pushout.inl (v b) (r₀ b)
local notation "b" => arithmeticZeroInfinityNormalizedTerminalTarget hπ data H m hj u hu
local notation "r" => arithmeticZeroInfinityNormalizedTerminalSide hπ data H m hj u hu
local notation "U" => arithmeticZeroInfinityNormalizedFullUnion hπ data H m hj u hu
local notation "F" => arithmeticZeroInfinityNormalizedFullComparison hπ data H m hj u hu
local notation "G" => arithmeticZeroInfinityNormalizedGlobalComparison hπ data H m hj u hu

/-- Both full retained nodes have their explicit original inclusions in the complete target. -/
def arithmeticZeroInfinityNormalizedGlobalRetainedChart (label : Bool) :
    arithmeticZeroDiagonalAtlasObject hπ data H m hj u hu (.retained ⟨0, by omega⟩ label) ⟶
      arithmeticZeroInfinityNormalizedGlobalTarget hπ data H m hj u hu :=
  k label ≫ pushout.inl b r

/-- The entire original retained charts keep their actual global comparison maps. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedGlobalComparison_retained (label : Bool) :
    c (.retained ⟨0, by omega⟩ label) ≫ (G).hom =
      arithmeticZeroInfinityNormalizedGlobalRetainedChart hπ data H m hj u hu label := by
  rw [← arithmeticZeroInfinityNormalizedRetainedPairSourceChart_global hπ data H m hj u hu label,
    Category.assoc, arithmeticZeroInfinityNormalizedGlobalComparison_pair,
    arithmeticZeroInfinityNormalizedRetainedPairSourceChart_comparison_assoc]
  rfl

/-- Both original closing equations hold on the complete independent target. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedGlobalRetainedChart_closing (label : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s label) ≫
      arithmeticZeroInfinityNormalizedGlobalRetainedChart hπ data H m hj u hu label =
        punctureOpen t label ≫ pushout.inr b r := by
  rw [← arithmeticZeroInfinityNormalizedGlobalComparison_retained,
    arithmeticZeroDiagonalAtlas_closing_normalized_assoc,
    arithmeticZeroInfinityNormalizedGlobalComparison_terminal]

/-- The complete normalized initial/infinity pair has one inclusion in the global target. -/
def arithmeticZeroInfinityNormalizedGlobalPairChart :
    arithmeticZeroInfinityNormalizedTargetPair data H m ⟶
      arithmeticZeroInfinityNormalizedGlobalTarget hπ data H m hj u hu :=
  b₀ false ≫ pushout.inl (b₀ false) (b₀ true) ≫ pushout.inl b r

/-- The opposite attachment has exactly the same full normalized initial/infinity pair. -/
theorem arithmeticZeroInfinityNormalizedGlobalPairChart_common :
    b₀ true ≫ pushout.inr (b₀ false) (b₀ true) ≫ pushout.inl b r =
      arithmeticZeroInfinityNormalizedGlobalPairChart hπ data H m hj u hu := by
  exact (pushout.condition_assoc _).symm

/-- The whole original initial/infinity union keeps its complete constructed pair comparison. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedGlobalComparison_fullUnion :
    (U).ι ≫ (G).hom = (F).hom ≫
      arithmeticZeroInfinityNormalizedGlobalPairChart hπ data H m hj u hu := by
  have h : (a₀ false ≫ pushout.inl (a₀ false) (a₀ true)) ≫ j = (U).ι := by
    rw [Category.assoc, arithmeticZeroInfinityNormalizedRetainedPairToGlobal_first,
      arithmeticZeroInfinityNormalizedRetainedToGlobal_pair]
  rw [← h, Category.assoc, Category.assoc,
    arithmeticZeroInfinityNormalizedGlobalComparison_pair,
    arithmeticZeroInfinityNormalizedRetainedPairIso_first_assoc,
    arithmeticZeroInfinityNormalizedRetainedPushoutIso_pair_assoc]
  rfl

end FLT.Mazur.WeierstrassDividedDepth

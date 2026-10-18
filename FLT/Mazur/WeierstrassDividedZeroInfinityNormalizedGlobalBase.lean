/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedTerminalGluing

/-!
# The complete exact-twist global comparison over the original base

The common terminal and both closing edges keep the full unreduced arithmetic
coefficient projection. The entire glued comparison is an isomorphism over
that original base.
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
local notation "t" => PolygonArithmeticSimultaneous.State.terminal D m
local notation "c" => arithmeticZeroDiagonalAtlasChart hπ data H m hj u hu
local notation "j" => arithmeticZeroInfinityNormalizedRetainedPairToGlobal hπ data H m hj u hu
local notation "E" => arithmeticZeroInfinityNormalizedRetainedPairIso hπ data H m hj u hu
local notation "a" => arithmeticZeroInfinityNormalizedTerminalSource hπ data H m hj u hu
local notation "b" => arithmeticZeroInfinityNormalizedTerminalTarget hπ data H m hj u hu
local notation "r" => arithmeticZeroInfinityNormalizedTerminalSide hπ data H m hj u hu
local notation "B" => arithmeticZeroDiagonalSourceToBase hπ data H m hj u hu
local notation "p" => arithmeticZeroInfinityNormalizedRetainedPairTargetToBase hπ data H m hj u hu
local notation "F" => arithmeticZeroInfinityNormalizedTerminalPushoutIso hπ data H m hj u hu
local notation "I" => arithmeticZeroInfinityNormalizedTerminalSourceIso hπ data H m hj u hu
local notation "G" => arithmeticZeroInfinityNormalizedGlobalComparison hπ data H m hj u hu

/-- Both full closing edges agree over the original unreduced arithmetic base. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedTerminalTarget_base :
    b ≫ p = r ≫ chartStructure Q t := by
  rw [← arithmeticZeroInfinityNormalizedTerminalSource_comparison_assoc,
    arithmeticZeroInfinityNormalizedRetainedPairIso_base,
    arithmeticZeroInfinityNormalizedTerminalSource_global_assoc,
    arithmeticZeroDiagonalAtlas_terminal_base]

/-- The complete independent exact-twist target retains the original arithmetic base. -/
def arithmeticZeroInfinityNormalizedGlobalTargetToBase :
    arithmeticZeroInfinityNormalizedGlobalTarget hπ data H m hj u hu ⟶ Spec (.of Q) :=
  pushout.desc p (chartStructure Q t)
    (arithmeticZeroInfinityNormalizedTerminalTarget_base hπ data H m hj u hu)

local notation "q" => arithmeticZeroInfinityNormalizedGlobalTargetToBase hπ data H m hj u hu

/-- The entire five-chart part retains its original coefficient projection. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedGlobalTargetToBase_pair :
    pushout.inl b r ≫ q = p := pushout.inl_desc _ _ _

/-- The entire common terminal retains its original coefficient projection. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedGlobalTargetToBase_terminal :
    pushout.inr b r ≫ q = chartStructure Q t := pushout.inr_desc _ _ _

/-- The full pushout comparison is over the original base on both entire source charts. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedTerminalPushoutIso_base :
    (F).hom ≫ q = (I).hom ≫ B := by
  apply pushout.hom_ext
  · rw [arithmeticZeroInfinityNormalizedTerminalPushoutIso_pair_assoc,
      arithmeticZeroInfinityNormalizedGlobalTargetToBase_pair,
      arithmeticZeroInfinityNormalizedRetainedPairIso_base,
      arithmeticZeroInfinityNormalizedTerminalSourceIso_pair_assoc]
  · rw [arithmeticZeroInfinityNormalizedTerminalPushoutIso_terminal_assoc,
      arithmeticZeroInfinityNormalizedGlobalTargetToBase_terminal,
      arithmeticZeroInfinityNormalizedTerminalSourceIso_terminal_assoc,
      arithmeticZeroDiagonalAtlas_terminal_base]

/-- The complete original arithmetic stage comparison preserves its full unreduced base. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedGlobalComparison_base :
    (G).hom ≫ q = B := by
  simp only [arithmeticZeroInfinityNormalizedGlobalComparison, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, arithmeticZeroInfinityNormalizedTerminalPushoutIso_base,
    Iso.inv_hom_id_assoc]

/-- The entire exact-twist comparison is an isomorphism over the original arithmetic base. -/
def arithmeticZeroInfinityNormalizedGlobalComparisonOver : Over.mk B ≅ Over.mk q :=
  Over.isoMk G (arithmeticZeroInfinityNormalizedGlobalComparison_base hπ data H m hj u hu)

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedTerminalRestriction

/-!
# The complete global comparison follows the original arithmetic quotients

Glue the full five-chart and common terminal quotient maps. The resulting
independent global target arrow agrees with the actual original global
quotient through the constructed entire comparison.
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
local notation "c" => fun k ↦ arithmeticZeroDiagonalAtlasChart hπ data H k hj u hu
local notation "j" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedPairToGlobal hπ data H k hj u hu
local notation "E" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedPairIso hπ data H k hj u hu
local notation "a" => fun k ↦ arithmeticZeroInfinityNormalizedTerminalSource hπ data H k hj u hu
local notation "b" => fun k ↦ arithmeticZeroInfinityNormalizedTerminalTarget hπ data H k hj u hu
local notation "r" => fun k ↦ arithmeticZeroInfinityNormalizedTerminalSide hπ data H k hj u hu
local notation "d" =>
  arithmeticZeroInfinityNormalizedRetainedPairPushoutRestriction hπ data H m hj u hu
local notation "e" =>
  arithmeticZeroInfinityNormalizedRetainedPairTargetRestriction hπ data H m hj u hu
local notation "S" => arithmeticZeroDiagonalAtlasRestriction hπ data H hj u hu m
  ArithmeticChartLabel.terminal
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H m 0 hj u hu
local notation "δ" => arithmeticZeroInfinityNormalizedTerminalOverlapRestriction (R := R) (π := π) m
local notation "I" => arithmeticZeroInfinityNormalizedTerminalSourceIso hπ data H m hj u hu
local notation "G" => fun k ↦ arithmeticZeroInfinityNormalizedGlobalComparison hπ data H k hj u hu
local notation "p" => fun k ↦ arithmeticZeroInfinityNormalizedGlobalTargetToBase hπ data H k hj u hu
local notation "B" => fun k ↦ arithmeticZeroDiagonalSourceToBase hπ data H k hj u hu

/-- The full independent global target keeps the whole pair and actual common terminal quotients. -/
def arithmeticZeroInfinityNormalizedGlobalTargetRestriction :
    arithmeticZeroInfinityNormalizedGlobalTarget hπ data H m hj u hu ⟶
      arithmeticZeroInfinityNormalizedGlobalTarget hπ data H (m + 1) hj u hu :=
  pushout.map (b m) (r m) (b (m + 1)) (r (m + 1)) e S δ
    (arithmeticZeroInfinityNormalizedTerminalTarget_restriction hπ data H m hj u hu)
    (arithmeticZeroInfinityNormalizedTerminalSide_restriction hπ data H m hj u hu)

local notation "ρ" => arithmeticZeroInfinityNormalizedGlobalTargetRestriction hπ data H m hj u hu

/-- The complete target quotient keeps the independently glued five-chart quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedGlobalTargetRestriction_pair :
    pushout.inl (b m) (r m) ≫ ρ = e ≫ pushout.inl (b (m + 1)) (r (m + 1)) :=
  pushout.inl_desc _ _ _

/-- The complete target quotient keeps the actual full common-terminal quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedGlobalTargetRestriction_terminal :
    pushout.inr (b m) (r m) ≫ ρ = S ≫ pushout.inr (b (m + 1)) (r (m + 1)) :=
  pushout.inr_desc _ _ _

/-- The entire global comparison follows the original full arithmetic quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedGlobalComparison_restriction :
    q ≫ (G (m + 1)).hom = (G m).hom ≫ ρ := by
  apply (cancel_epi (I).hom).mp
  apply pushout.hom_ext
  · rw [arithmeticZeroInfinityNormalizedTerminalSourceIso_pair_assoc,
      arithmeticZeroInfinityNormalizedTerminalSourceIso_pair_assoc,
      arithmeticZeroInfinityNormalizedGlobalComparison_pair_assoc,
      arithmeticZeroInfinityNormalizedGlobalTargetRestriction_pair,
      ← arithmeticZeroInfinityNormalizedRetainedPairPushoutRestriction_global_assoc,
      arithmeticZeroInfinityNormalizedGlobalComparison_pair,
      arithmeticZeroInfinityNormalizedRetainedPairPushoutRestriction_comparison_assoc]
  · rw [arithmeticZeroInfinityNormalizedTerminalSourceIso_terminal_assoc,
      arithmeticZeroInfinityNormalizedTerminalSourceIso_terminal_assoc,
      arithmeticZeroInfinityNormalizedGlobalComparison_terminal_assoc,
      arithmeticZeroInfinityNormalizedGlobalTargetRestriction_terminal,
      ← arithmeticZeroDiagonalAtlasChart_restriction_assoc,
      arithmeticZeroInfinityNormalizedGlobalComparison_terminal]

/-- The entire independent quotient retains the full original arithmetic base square. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedGlobalTargetRestriction_base :
    ρ ≫ p (m + 1) = p m ≫ baseRestriction R π m := by
  apply (cancel_epi (G m).hom).mp
  rw [← arithmeticZeroInfinityNormalizedGlobalComparison_restriction_assoc,
    arithmeticZeroInfinityNormalizedGlobalComparison_base,
    arithmeticZeroInfinityNormalizedGlobalComparison_base_assoc,
    arithmeticZeroDiagonalSourceToBase_restriction]

end FLT.Mazur.WeierstrassDividedDepth

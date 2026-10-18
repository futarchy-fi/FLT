/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedGlobalBase

/-!
# Quotient squares on the complete common terminal attachment

The coproduct of the original closing-edge quotient maps follows the entire
terminal and both five-chart comparisons. No reduced coefficient map enters.
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
local notation "Q" => Quotient R π
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "t" => PolygonArithmeticSimultaneous.State.terminal D
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
local notation "ρ" => closingOverlapRestriction (R := R) (π := π) m

/-- Both whole original closing edges keep their full coefficient quotient maps. -/
def arithmeticZeroInfinityNormalizedTerminalOverlapRestriction :
    branchTorus (Q m) ⨿ branchTorus (Q m) ⟶
      branchTorus (Q (m + 1)) ⨿ branchTorus (Q (m + 1)) := coprod.map ρ ρ

local notation "δ" => arithmeticZeroInfinityNormalizedTerminalOverlapRestriction (R := R) (π := π) m

omit [IsBezout R] in
/-- Each full original terminal puncture follows the actual corrected terminal quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedTerminalPuncture_restriction (label : Bool) :
    punctureOpen (t m) label ≫ S = ρ ≫ punctureOpen (t (m + 1)) label := by
  rw [arithmeticZeroDiagonalAtlasRestriction_terminal]
  exact punctureOpen_ringMap (restriction R π m).toRingHom _ _
    ((arithmeticZeroDiagonalState_compatible hπ data H 0 hj u hu).2.2.1 m) label

omit [IsBezout R] in
/-- Both closing punctures together follow the quotient of their one entire common terminal. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedTerminalSide_restriction :
    r m ≫ S = δ ≫ r (m + 1) := by
  apply coprod.hom_ext <;>
    simp only [arithmeticZeroInfinityNormalizedTerminalSide,
      arithmeticZeroInfinityNormalizedTerminalOverlapRestriction,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, coprod.inl_map_assoc,
      coprod.inr_map_assoc, coprod.inl_desc, coprod.inr_desc,
      arithmeticZeroInfinityNormalizedTerminalPuncture_restriction]

/-- The full source boundary square uses the actual original five-chart quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedTerminalSource_restriction :
    a m ≫ d = δ ≫ a (m + 1) := by
  apply (cancel_mono (j (m + 1))).mp
  rw [Category.assoc, arithmeticZeroInfinityNormalizedRetainedPairPushoutRestriction_global,
    arithmeticZeroInfinityNormalizedTerminalSource_global_assoc,
    ← arithmeticZeroDiagonalAtlasChart_restriction,
    arithmeticZeroInfinityNormalizedTerminalSide_restriction_assoc,
    Category.assoc, arithmeticZeroInfinityNormalizedTerminalSource_global]

/-- The full independent target boundary square preserves both complete closing equations. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedTerminalTarget_restriction :
    b m ≫ e = δ ≫ b (m + 1) := by
  rw [← arithmeticZeroInfinityNormalizedTerminalSource_comparison_assoc,
    ← arithmeticZeroInfinityNormalizedRetainedPairPushoutRestriction_comparison,
    arithmeticZeroInfinityNormalizedTerminalSource_restriction_assoc,
    arithmeticZeroInfinityNormalizedTerminalSource_comparison]

end FLT.Mazur.WeierstrassDividedDepth

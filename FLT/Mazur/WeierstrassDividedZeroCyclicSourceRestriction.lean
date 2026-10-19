/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclicInitialRestriction
public import FLT.Mazur.PolygonSmoothingBranchSwapNaturality

/-!
# All five actual source-node quotient squares

The seed coefficient maps retain the full diagonal smoothings. On both true
nodes, naturality of the entire branch swap gives the reflected square.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticZeroDiagonalAtlasChart
  arithmeticZeroCyclicInitialChart simultaneousTwistedArithmeticRestriction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => fun k ↦ Quotient R π k
local notation "S" => arithmeticZeroCyclicSeed hπ data H hj u hu
local notation "hS" => arithmeticZeroCyclicSeed_compatible hπ data H hj u hu
local notation "c" => fun k ↦ arithmeticZeroCyclicSourceChart hπ data H k hj u hu
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H m 0 hj u hu

/-- The original full smoothing coefficient map on each cyclic seed node. -/
def arithmeticZeroCyclicSourceNodeRestriction (i : ZeroCyclicVertex) :
    PolygonSmoothing.chart (Q m) ((S).parameter m i) ⟶
      PolygonSmoothing.chart (Q (m + 1)) ((S).parameter (m + 1) i) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom
    ((S).parameter (m + 1) i) ((S).parameter m i) ((hS).1 m i)))

local notation "r" => arithmeticZeroCyclicSourceNodeRestriction hπ data H m hj u hu

/-- The common terminal uses its actual corrected full node quotient. -/
theorem arithmeticZeroCyclicSourceNodeRestriction_terminal :
    r .terminal = arithmeticZeroDiagonalAtlasRestriction hπ data H hj u hu m .terminal := by
  rw [arithmeticZeroDiagonalAtlasRestriction_terminal]
  rfl

/-- The two retained seed nodes use the full original diagonal quotients. -/
theorem arithmeticZeroCyclicSourceNodeRestriction_retained (b : Bool) :
    r (.retained b) =
      arithmeticZeroDiagonalAtlasRestriction hπ data H hj u hu m (.retained ⟨0, by omega⟩ b) := by
  rw [arithmeticZeroDiagonalAtlasRestriction_last]
  rfl

/-- Both initial seed nodes retain the original full normalized smoothing quotient. -/
theorem arithmeticZeroCyclicSourceNodeRestriction_initial (b : Bool) :
    r (.initial b) = closingNormalizedRestriction data H m := rfl

/-- All five entire seed inclusions commute with the actual original global quotient. -/
@[reassoc] theorem arithmeticZeroCyclicSourceChart_restriction (i : ZeroCyclicVertex) :
    c m i ≫ q = r i ≫ c (m + 1) i := by
  rcases i with _ | (_ | _) | (_ | _)
  · rw [arithmeticZeroCyclicSourceNodeRestriction_terminal]
    exact (arithmeticZeroDiagonalAtlasChart_restriction hπ data H hj u hu m .terminal).symm
  · rw [arithmeticZeroCyclicSourceNodeRestriction_retained]
    exact (arithmeticZeroDiagonalAtlasChart_restriction hπ data H hj u hu m
      (.retained ⟨0, by omega⟩ false)).symm
  · dsimp only [arithmeticZeroCyclicSourceChart]
    rw [Category.assoc, ← arithmeticZeroDiagonalAtlasChart_restriction,
      ← arithmeticZeroCyclicSourceNodeRestriction_retained,
      arithmeticZeroCyclicSourceNodeRestriction]
    dsimp only [arithmeticZeroCyclicSeed]
    rw [branchSwapIso_ringMap_assoc]
  · rw [arithmeticZeroCyclicSourceNodeRestriction_initial]
    exact arithmeticZeroCyclicInitialChart_restriction hπ data H m hj u hu false
  · dsimp only [arithmeticZeroCyclicSourceChart]
    rw [Category.assoc, arithmeticZeroCyclicInitialChart_restriction,
      ← arithmeticZeroCyclicSourceNodeRestriction_initial hπ data H m hj u hu true,
      arithmeticZeroCyclicSourceNodeRestriction]
    dsimp only [arithmeticZeroCyclicSeed]
    rw [branchSwapIso_ringMap_assoc]

end FLT.Mazur.WeierstrassDividedDepth

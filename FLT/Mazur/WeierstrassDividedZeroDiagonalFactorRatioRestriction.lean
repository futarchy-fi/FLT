/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInitialTotalRestriction

/-!
# The full transported initial factor ratio commutes with arithmetic restriction

The original polynomial coefficient square transports through the complete open
and node comparisons, retaining the actual diagonal smoothing at each order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "ρ" => arithmeticFullInitialNodeQuotient R π m W (π ^ 1)
local notation "N" => fun k ↦ arithmeticInitialFactorRatioChart π k W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "E" => fun k ↦ arithmeticZeroDiagonalInitialOpenIso hπ data H k hj u hu
local notation "F" => fun k ↦ arithmeticZeroDiagonalInitialFactorRatio hπ data H k hj u hu
local notation "T" => fun k ↦ arithmeticZeroDiagonalInitialTotalNodeIso hπ data H k hj u hu
local notation "S" => arithmeticZeroDiagonalInitialRestriction hπ data H 0 hj u hu m
local notation "U" => arithmeticZeroDiagonalInitialNodeRestriction hπ data H 0 hj u hu m

omit [IsDomain R] [IsBezout R] in
/-- The original full factor ratio has the concrete normalized node coefficient map. -/
@[reassoc] theorem arithmeticInitialFactorRatioChart_closingRestriction :
    ρ ≫ N (m + 1) = N m ≫ closingNormalizedRestriction data H m :=
  arithmeticInitialFactorRatioChart_restriction π m W (π ^ 1)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)

/-- The full corrected initial map follows the actual diagonal source and target quotients. -/
@[reassoc] theorem arithmeticZeroDiagonalInitialFactorRatio_restriction (b : Bool) :
    S b ≫ F (m + 1) b = F m b ≫ U b := by
  apply (cancel_epi (E m b).hom).mp
  rw [← Category.assoc, arithmeticZeroDiagonalInitialOpenIso_restriction,
    Category.assoc, arithmeticZeroDiagonalInitialFactorRatio_transport]
  rw [← Category.assoc, arithmeticInitialFactorRatioChart_closingRestriction,
    Category.assoc, arithmeticZeroDiagonalInitialTotalNodeIso_restriction,
    ← arithmeticZeroDiagonalInitialFactorRatio_transport_assoc]

end FLT.Mazur.WeierstrassDividedDepth

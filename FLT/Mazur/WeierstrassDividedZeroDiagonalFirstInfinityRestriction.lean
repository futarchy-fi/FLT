/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalFirstInfinityIso
public import FLT.Mazur.WeierstrassDividedZeroDiagonalInfinityComparisonRestriction

/-!
# The complete first source node follows the original quotient system

Transport the full node quotient through the proved node isomorphisms, then
identify both chart restrictions and the original global quotient arrow.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
  arithmeticZeroFiniteAtlasIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "N" => fun k ↦ arithmeticZeroDiagonalFirstInfinityNodeMap hπ data H k hj u hu
local notation "l" => fun k ↦ arithmeticZeroDiagonalInitialOverlap hπ data H k hj u hu false
local notation "i" => fun k ↦ arithmeticZeroDiagonalOverlapToInfinity hπ data H k hj u hu
local notation "C" => fun k ↦ arithmeticZeroDiagonalPolygonInitialMap hπ data H k hj u hu false
local notation "g" => fun k ↦ arithmeticZeroDiagonalFactorRatioInfinityMap hπ data H k hj u hu
local notation "S" => arithmeticZeroDiagonalAtlasRestriction hπ data H hj u hu m
local notation "t" => arithmeticZeroDiagonalInitialNodeRestriction hπ data H 0 hj u hu m false
local notation "G" => fun k ↦ arithmeticZeroDiagonalFirstInfinityToGlobal hπ data H k hj u hu
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H m 0 hj u hu

/-- The complete first source node carries the actual diagonal node coefficient quotient. -/
def arithmeticZeroDiagonalFirstInfinityRestriction :
    arithmeticZeroDiagonalFirstInfinityPushout hπ data H m hj u hu ⟶
      arithmeticZeroDiagonalFirstInfinityPushout hπ data H (m + 1) hj u hu :=
  N m ≫ t ≫ inv (N (m + 1))

local notation "r" => arithmeticZeroDiagonalFirstInfinityRestriction hπ data H m hj u hu

/-- The whole constructed source-node quotient keeps its exact target-node square. -/
@[reassoc] theorem arithmeticZeroDiagonalFirstInfinityRestriction_node :
    r ≫ N (m + 1) = N m ≫ t := by
  simp only [arithmeticZeroDiagonalFirstInfinityRestriction, Category.assoc,
    IsIso.inv_hom_id, Category.comp_id]

/-- On the complete initial chart, this is the original corrected source quotient. -/
@[reassoc] theorem arithmeticZeroDiagonalFirstInfinityRestriction_initial :
    pushout.inr (i m) (l m) ≫ r = S (.initial false) ≫
      pushout.inr (i (m + 1)) (l (m + 1)) := by
  apply (cancel_mono (N (m + 1))).mp
  rw [Category.assoc, arithmeticZeroDiagonalFirstInfinityRestriction_node,
    arithmeticZeroDiagonalFirstInfinityNodeMap_initial_assoc, Category.assoc,
    arithmeticZeroDiagonalFirstInfinityNodeMap_initial,
    arithmeticZeroDiagonalAtlasRestriction_initial,
    arithmeticZeroDiagonalInitialFactorRatio_restriction]

/-- On the complete infinity chart, this is the unchanged original cubic quotient. -/
@[reassoc] theorem arithmeticZeroDiagonalFirstInfinityRestriction_infinity :
    pushout.inl (i m) (l m) ≫ r = S .infinity ≫
      pushout.inl (i (m + 1)) (l (m + 1)) := by
  apply (cancel_mono (N (m + 1) ≫ C (m + 1))).mp
  simp only [Category.assoc]
  rw [arithmeticZeroDiagonalFirstInfinityRestriction_node_assoc,
    arithmeticZeroDiagonalFirstInfinityNodeMap_infinity_polygon,
    arithmeticZeroDiagonalFactorRatioInfinityMap_restriction,
    ← arithmeticZeroDiagonalPolygonInitialMap_restriction,
    arithmeticZeroDiagonalFirstInfinityNodeMap_infinity_polygon_assoc]

/-- The full node quotient is the restriction of the actual original global quotient. -/
@[reassoc] theorem arithmeticZeroDiagonalFirstInfinityRestriction_global :
    r ≫ G (m + 1) = G m ≫ q := by
  apply pushout.hom_ext
  · rw [arithmeticZeroDiagonalFirstInfinityRestriction_infinity_assoc,
      arithmeticZeroDiagonalFirstInfinityToGlobal_infinity,
      arithmeticZeroDiagonalFirstInfinityToGlobal_infinity_assoc]
    exact arithmeticZeroDiagonalAtlasChart_restriction hπ data H hj u hu m .infinity
  · rw [arithmeticZeroDiagonalFirstInfinityRestriction_initial_assoc,
      arithmeticZeroDiagonalFirstInfinityToGlobal_initial,
      arithmeticZeroDiagonalFirstInfinityToGlobal_initial_assoc]
    exact arithmeticZeroDiagonalAtlasChart_restriction hπ data H hj u hu m (.initial false)

end FLT.Mazur.WeierstrassDividedDepth

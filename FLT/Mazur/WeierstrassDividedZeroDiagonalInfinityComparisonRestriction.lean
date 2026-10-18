/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalInfinityRestriction
public import FLT.Mazur.WeierstrassDividedZeroDiagonalPolygonComparisonRestriction

/-!
# Naturality of the full diagonal infinity comparison

The transported right boundary uses the full accumulated node quotient, so the
whole original infinity map follows the independent polygon restriction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
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
local notation "B" => fun k ↦ arithmeticZeroDiagonalInitialInfinityBoundary hπ data H k hj u hu
local notation "T" => fun k ↦ arithmeticZeroDiagonalInitialTotalNodeIso hπ data H k hj u hu
local notation "P" => fun k ↦ arithmeticZeroDiagonalInfinityParameterIso hπ data H k hj u hu
local notation "f" => fun k ↦ arithmeticZeroDiagonalFactorRatioInfinityMap hπ data H k hj u hu
local notation "ρ" => arithmeticZeroDiagonalPolygonRestriction hπ data H m hj u hu
local notation "c" => closingOverlapRestriction (R := R) (π := π) m

omit [IsBezout R] in
/-- Both transported infinity boundaries preserve their full original quotient square. -/
@[reassoc] theorem arithmeticZeroDiagonalInitialInfinityBoundary_restriction (b : Bool) :
    B m b ≫ ρ = c ≫ B (m + 1) b := by
  simp only [arithmeticZeroDiagonalInitialInfinityBoundary, Category.assoc,
    arithmeticZeroDiagonalPolygonInitialMap_restriction]
  rw [← Category.assoc (T m b).hom,
    ← arithmeticZeroDiagonalInitialTotalNodeIso_restriction]
  simp only [closingNormalizedRestriction, closingOverlapRestriction,
    Category.assoc, factorRatioRightBranch_coefficient_assoc]

/-- The full original infinity comparison follows the actual source and target quotients. -/
@[reassoc] theorem arithmeticZeroDiagonalFactorRatioInfinityMap_restriction :
    arithmeticZeroDiagonalAtlasRestriction hπ data H hj u hu m .infinity ≫ f (m + 1) =
      f m ≫ ρ := by
  simp only [arithmeticZeroDiagonalFactorRatioInfinityMap, Category.assoc,
    arithmeticZeroDiagonalInitialInfinityBoundary_restriction]
  rw [← Category.assoc, arithmeticZeroDiagonalInfinityParameterIso_restriction,
    Category.assoc]

/-- The independently constructed polygon at all arithmetic quotient orders. -/
def arithmeticZeroDiagonalPolygonSystem : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun k ↦ arithmeticZeroDiagonalPolygonRestriction hπ data H k hj u hu)

/-- The complete infinity comparison is a morphism of arithmetic quotient systems. -/
def arithmeticZeroDiagonalInfinityComparisonSystem :
    arithmeticZeroDiagonalChartSystem hπ data H hj u hu .infinity ⟶
      arithmeticZeroDiagonalPolygonSystem hπ data H hj u hu :=
  NatTrans.ofSequence (fun k ↦ f k) (by
    intro k
    simpa only [arithmeticZeroDiagonalChartSystem, arithmeticZeroDiagonalPolygonSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
      arithmeticZeroDiagonalFactorRatioInfinityMap_restriction hπ data H k hj u hu)

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclicSourceCharts

/-!
# The five exact cyclic edges in the original global source

Both closing edges retain the common terminal. The true retained edge uses
the inverse of the entire accumulated Laurent substitution.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] arithmeticZeroDiagonalAtlasChart
  arithmeticZeroCyclicInitialChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "S" => arithmeticZeroCyclicSeed hπ data H hj u hu
local notation "c" => arithmeticZeroDiagonalAtlasChart hπ data H m hj u hu
local notation "a" => arithmeticZeroCyclicInitialChart hπ data H m hj u hu
local notation "f" => arithmeticZeroCyclicSourceChart hπ data H m hj u hu
local notation "E" => fun b ↦ punctureSpecIso
  (arithmeticZeroRetainedEdgeEquiv hπ data H m hj u hu b)

/-- The entire original retained attachment agrees with each unreflected initial node. -/
@[reassoc] theorem arithmeticZeroCyclicInitialChart_retained (b : Bool) :
    leftBranchOpen Q τ ≫ a b =
      (E b).hom ≫ rightBranchOpen Q ((D).last m b) ≫
        c (.retained ⟨0, by omega⟩ b) := by
  rw [arithmeticZeroCyclicInitialChart_left, ← Category.assoc,
    arithmeticZeroRetainedEdgeEquiv_side, arithmeticZeroInfinityNormalizedRetainedSide_global]

/-- All five full seed edges hold in the actual original corrected global stage. -/
@[reassoc] theorem arithmeticZeroCyclicSourceChart_edge (i : ZeroCyclicVertex) :
    leftBranchOpen Q ((S).parameter m i) ≫ f i =
      (punctureSpecIso ((S).edge m i)).hom ≫
        rightBranchOpen Q ((S).parameter m (zeroCyclicSuccessor i)) ≫
          f (zeroCyclicSuccessor i) := by
  rcases i with _ | (_ | _) | (_ | _)
  · change leftBranchOpen Q ((D).terminal m) ≫ c .terminal =
      (edgeInversion Q).hom ≫ rightBranchOpen Q ((D).last m true) ≫
        (branchSwapIso Q ((D).last m true)).hom ≫ c (.retained ⟨0, by omega⟩ true)
    rw [rightBranchOpen_branchSwapIso_assoc]
    simpa only [punctureOpen_true] using
      (arithmeticZeroDiagonalAtlas_closing_normalized hπ data H m hj u hu true).symm
  · change leftBranchOpen Q ((D).last m false) ≫ c (.retained ⟨0, by omega⟩ false) =
      (edgeInversion Q).hom ≫ rightBranchOpen Q ((D).terminal m) ≫ c .terminal
    rw [← punctureOpen_false,
      ← arithmeticZeroDiagonalAtlas_closing_normalized hπ data H m hj u hu false,
      ← Category.assoc, LaurentUnitPoints.edgeInversion_comp_self, Category.id_comp]
  · change leftBranchOpen Q ((D).last m true) ≫
      (branchSwapIso Q ((D).last m true)).hom ≫ c (.retained ⟨0, by omega⟩ true) =
        (punctureSpecIso (arithmeticZeroRetainedEdgeEquiv hπ data H m hj u hu true).symm).hom ≫
          rightBranchOpen Q τ ≫ (branchSwapIso Q τ).hom ≫ a true
    rw [leftBranchOpen_branchSwapIso_assoc, rightBranchOpen_branchSwapIso_assoc,
      punctureSpecIso_symm, Iso.symm_hom, arithmeticZeroCyclicInitialChart_retained]
    simp only [Iso.inv_hom_id_assoc]
  · exact arithmeticZeroCyclicInitialChart_retained hπ data H m hj u hu false
  · change leftBranchOpen Q τ ≫ (branchSwapIso Q τ).hom ≫ a true =
      (edgeInversion Q).hom ≫ rightBranchOpen Q τ ≫ a false
    rw [leftBranchOpen_branchSwapIso_assoc,
      arithmeticZeroCyclicInitialChart_common, ← Category.assoc,
      LaurentUnitPoints.edgeInversion_comp_self, Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth

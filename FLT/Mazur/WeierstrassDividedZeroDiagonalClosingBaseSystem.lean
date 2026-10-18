/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalClosingBase
public import FLT.Mazur.WeierstrassDividedZeroDiagonalFirstInfinitySystem

/-!
# Full diagonal source coefficient maps commute with arithmetic quotients

The transported original global base, the actual first union and both full
closing unions use the same original quotient coefficient arrows.
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
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H m 0 hj u hu
local notation "B" => fun k ↦ arithmeticZeroDiagonalSourceToBase hπ data H k hj u hu
local notation "U" => fun k ↦ arithmeticZeroDiagonalClosingUnion hπ data H k hj u hu
local notation "ρ" => arithmeticZeroDiagonalClosingUnionRestriction hπ data H m hj u hu

/-- The entire original global source retains its exact quotient coefficient arrow. -/
@[reassoc] theorem arithmeticZeroDiagonalSourceToBase_restriction :
    q ≫ B (m + 1) = B m ≫ baseRestriction R π m := by
  simp only [simultaneousTwistedArithmeticRestriction, arithmeticZeroDiagonalSourceToBase,
    Category.assoc, Iso.hom_inv_id_assoc, finiteGlobalArithmeticRestriction_structure]

/-- The actual first union retains the same full original coefficient restriction. -/
@[reassoc] theorem arithmeticZeroDiagonalFirstInfinityUnionRestriction_base :
    arithmeticZeroDiagonalFirstInfinityUnionRestriction hπ data H m hj u hu ≫
      (arithmeticZeroDiagonalFirstInfinityUnion hπ data H (m + 1) hj u hu).ι ≫ B (m + 1) =
      (arithmeticZeroDiagonalFirstInfinityUnion hπ data H m hj u hu).ι ≫
        B m ≫ baseRestriction R π m := by
  rw [arithmeticZeroDiagonalFirstInfinityUnionRestriction_global_assoc,
    arithmeticZeroDiagonalSourceToBase_restriction]

/-- Each entire closing union retains the original quotient on its arithmetic base. -/
@[reassoc] theorem arithmeticZeroDiagonalClosingUnionRestriction_base (b : Bool) :
    ρ b ≫ (U (m + 1) b).ι ≫ B (m + 1) =
      (U m b).ι ≫ B m ≫ baseRestriction R π m := by
  rw [arithmeticZeroDiagonalClosingUnionRestriction_global_assoc,
    arithmeticZeroDiagonalSourceToBase_restriction]

/-- Both whole original closing unions form arithmetic quotient systems. -/
def arithmeticZeroDiagonalClosingUnionSystem (b : Bool) : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun k ↦ arithmeticZeroDiagonalClosingUnionRestriction hπ data H k hj u hu b)

/-- Each whole closing union has its natural original arithmetic coefficient projection. -/
def arithmeticZeroDiagonalClosingUnionSystemStructure (b : Bool) :
    arithmeticZeroDiagonalClosingUnionSystem hπ data H hj u hu b ⟶ baseSystem R π :=
  NatTrans.ofSequence (fun k ↦ (U k b).ι ≫ B k) (by
    intro k
    simpa only [arithmeticZeroDiagonalClosingUnionSystem, baseSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ, Category.assoc] using
      arithmeticZeroDiagonalClosingUnionRestriction_base hπ data H k hj u hu b)

/-- The complete closing comparison commutes with every original arithmetic quotient. -/
def arithmeticZeroDiagonalClosingUnionSystemComparison (b : Bool) :
    arithmeticZeroDiagonalClosingUnionSystem hπ data H hj u hu b ⟶
      arithmeticZeroDiagonalPolygonSystem hπ data H hj u hu :=
  NatTrans.ofSequence (fun k ↦ arithmeticZeroDiagonalClosingUnionMap hπ data H k hj u hu b) (by
    intro k
    simpa only [arithmeticZeroDiagonalClosingUnionSystem, arithmeticZeroDiagonalPolygonSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
      arithmeticZeroDiagonalClosingUnionMap_restriction hπ data H k hj u hu b)

/-- Nonconsecutive orders keep the full original coefficient square on each closing union. -/
@[reassoc] theorem arithmeticZeroDiagonalClosingUnionSystemStructure_naturality
    (b : Bool) {i j : ℕ} (hij : i ≤ j) :
    (arithmeticZeroDiagonalClosingUnionSystem hπ data H hj u hu b).map (homOfLE hij) ≫
      (U j b).ι ≫ B j = (U i b).ι ≫ B i ≫ (baseSystem R π).map (homOfLE hij) := by
  exact ((arithmeticZeroDiagonalClosingUnionSystemStructure hπ data H hj u hu b).naturality
    (homOfLE hij)).trans (Category.assoc _ _ _)

end FLT.Mazur.WeierstrassDividedDepth

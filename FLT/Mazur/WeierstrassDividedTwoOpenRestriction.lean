/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowOpenRestriction
public import FLT.Mazur.WeierstrassDividedTwoNodeRestriction

/-!
# Quotient squares for the finite corrected initial open

The original initial-node coefficient map transports through the actual
pullback isomorphisms. Its node square uses the exact changed smoothing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (k m : ℕ)
local notation "A" => fun l ↦ arithmeticTwoFiniteInitialObject hπ data H k l hj u hu
local notation "I" => fun l ↦ arithmeticTwoFiniteInitialIso hπ data H k l hj u hu
local notation "F" => fun l ↦ arithmeticTwoFiniteInitialNodeChart hπ data H k l hj u hu
local notation "M" => fun k ↦ arithmeticFifthShallowNodeChart hπ data H k 2 hj u hu
local notation "C" => fun l ↦ arithmeticTwoFiniteInitialNodeIso hπ data H k l hj u hu
local notation "ρ" => arithmeticFifthShallowOpenRestriction hπ data H 2 hj u hu m

/-- The full original coefficient map transported to the corrected initial opens. -/
def arithmeticTwoFiniteInitialRestriction (b : Bool) : A m b ⟶ A (m + 1) b :=
  (I m b).inv ≫ ρ b ≫ (I (m + 1) b).hom

local notation "S" => arithmeticTwoFiniteInitialRestriction hπ data H hj u hu k m

/-- The full initial comparison is an exact square for the original quotient. -/
@[reassoc] theorem arithmeticTwoFiniteInitialIso_restriction (b : Bool) :
    (I m b).hom ≫ S b = ρ b ≫ (I (m + 1) b).hom := by
  rw [arithmeticTwoFiniteInitialRestriction, Iso.hom_inv_id_assoc]

/-- The whole corrected initial open has the coefficient map of its actual new smoothing. -/
@[reassoc] theorem arithmeticTwoFiniteInitialNodeChart_restriction (b : Bool) :
    S b ≫ F (m + 1) b =
      F m b ≫ arithmeticTwoFiniteInitialNodeRestriction hπ data H hj u hu k m b := by
  apply (cancel_epi (I m b).hom).mp
  rw [← Category.assoc, arithmeticTwoFiniteInitialIso_restriction,
    Category.assoc, arithmeticTwoFiniteInitialIso_nodeChart]
  rw [← Category.assoc, arithmeticFifthShallowNodeChart_restriction, Category.assoc]
  change (M m b ≫ arithmeticFifthShallowNodeRestriction hπ data H 2 hj u hu m b ≫
    (C (m + 1) b).hom) = _
  rw [arithmeticTwoFiniteInitialNodeIso_restriction,
    ← arithmeticTwoFiniteInitialIso_nodeChart_assoc]

end FLT.Mazur.WeierstrassDividedDepth

/-!
# Quotient squares for the diagonal corrected initial open

The correction count changes across each quotient. The initial-open map
retains the coefficient square on the actual diagonal node smoothing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "A" => fun l ↦ arithmeticTwoFiniteInitialObject hπ data H l l hj u hu
local notation "I" => fun l ↦ arithmeticTwoFiniteInitialIso hπ data H l l hj u hu
local notation "F" => fun l ↦ arithmeticTwoFiniteInitialNodeChart hπ data H l l hj u hu
local notation "M" => fun k ↦ arithmeticFifthShallowNodeChart hπ data H k 2 hj u hu
local notation "C" => fun l ↦ arithmeticTwoFiniteInitialNodeIso hπ data H l l hj u hu
local notation "ρ" => arithmeticFifthShallowOpenRestriction hπ data H 2 hj u hu m

/-- The full original coefficient map transported to the corrected initial opens. -/
def arithmeticTwoDiagonalInitialRestriction (b : Bool) : A m b ⟶ A (m + 1) b :=
  (I m b).inv ≫ ρ b ≫ (I (m + 1) b).hom

local notation "S" => arithmeticTwoDiagonalInitialRestriction hπ data H hj u hu m

/-- The full initial comparison is an exact square for the original quotient. -/
@[reassoc] theorem arithmeticTwoDiagonalInitialIso_restriction (b : Bool) :
    (I m b).hom ≫ S b = ρ b ≫ (I (m + 1) b).hom := by
  rw [arithmeticTwoDiagonalInitialRestriction, Iso.hom_inv_id_assoc]

/-- The whole corrected initial open has the coefficient map of its actual new smoothing. -/
@[reassoc] theorem arithmeticTwoDiagonalInitialNodeChart_restriction (b : Bool) :
    S b ≫ F (m + 1) b =
      F m b ≫ arithmeticTwoDiagonalInitialNodeRestriction hπ data H hj u hu m b := by
  apply (cancel_epi (I m b).hom).mp
  rw [← Category.assoc, arithmeticTwoDiagonalInitialIso_restriction,
    Category.assoc, arithmeticTwoFiniteInitialIso_nodeChart]
  rw [← Category.assoc, arithmeticFifthShallowNodeChart_restriction, Category.assoc]
  change (M m b ≫ arithmeticFifthShallowNodeRestriction hπ data H 2 hj u hu m b ≫
    (C (m + 1) b).hom) = _
  rw [arithmeticTwoDiagonalInitialNodeIso_restriction,
    ← arithmeticTwoFiniteInitialIso_nodeChart_assoc]

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthFartherOpenRestriction
public import FLT.Mazur.WeierstrassDividedThreeNodeRestriction

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
  (H : ArithmeticAtlasCoefficients data) (hj : 4 ≤ n)
  (u : Rˣ) (hu : (data ⟨4, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (k m : ℕ)
local notation "A" => fun l ↦ arithmeticThreeFiniteInitialObject hπ data H k l hj u hu
local notation "I" => fun l ↦ arithmeticThreeFiniteInitialIso hπ data H k l hj u hu
local notation "F" => fun l ↦ arithmeticThreeFiniteInitialNodeChart hπ data H k l hj u hu
local notation "M" => fun k ↦ arithmeticFifthFartherNodeChart hπ data H k 3 hj u hu
local notation "C" => fun l ↦ arithmeticThreeFiniteInitialNodeIso hπ data H k l hj u hu
local notation "ρ" => arithmeticFifthFartherOpenRestriction hπ data H 3 hj u hu m

/-- The full original coefficient map transported to the corrected initial opens. -/
def arithmeticThreeFiniteInitialRestriction (b : Bool) : A m b ⟶ A (m + 1) b :=
  (I m b).inv ≫ ρ b ≫ (I (m + 1) b).hom

local notation "S" => arithmeticThreeFiniteInitialRestriction hπ data H hj u hu k m

/-- The full initial comparison is an exact square for the original quotient. -/
@[reassoc] theorem arithmeticThreeFiniteInitialIso_restriction (b : Bool) :
    (I m b).hom ≫ S b = ρ b ≫ (I (m + 1) b).hom := by
  rw [arithmeticThreeFiniteInitialRestriction, Iso.hom_inv_id_assoc]

/-- The whole corrected initial open has the coefficient map of its actual new smoothing. -/
@[reassoc] theorem arithmeticThreeFiniteInitialNodeChart_restriction (b : Bool) :
    S b ≫ F (m + 1) b =
      F m b ≫ arithmeticThreeFiniteInitialNodeRestriction hπ data H hj u hu k m b := by
  apply (cancel_epi (I m b).hom).mp
  rw [← Category.assoc, arithmeticThreeFiniteInitialIso_restriction,
    Category.assoc, arithmeticThreeFiniteInitialIso_nodeChart]
  rw [← Category.assoc, arithmeticFifthFartherNodeChart_restriction, Category.assoc]
  change (M m b ≫ arithmeticFifthFartherNodeRestriction hπ data H 3 hj u hu m b ≫
    (C (m + 1) b).hom) = _
  rw [arithmeticThreeFiniteInitialNodeIso_restriction,
    ← arithmeticThreeFiniteInitialIso_nodeChart_assoc]

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
  (H : ArithmeticAtlasCoefficients data) (hj : 4 ≤ n)
  (u : Rˣ) (hu : (data ⟨4, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "A" => fun l ↦ arithmeticThreeFiniteInitialObject hπ data H l l hj u hu
local notation "I" => fun l ↦ arithmeticThreeFiniteInitialIso hπ data H l l hj u hu
local notation "F" => fun l ↦ arithmeticThreeFiniteInitialNodeChart hπ data H l l hj u hu
local notation "M" => fun k ↦ arithmeticFifthFartherNodeChart hπ data H k 3 hj u hu
local notation "C" => fun l ↦ arithmeticThreeFiniteInitialNodeIso hπ data H l l hj u hu
local notation "ρ" => arithmeticFifthFartherOpenRestriction hπ data H 3 hj u hu m

/-- The full original coefficient map transported to the corrected initial opens. -/
def arithmeticThreeDiagonalInitialRestriction (b : Bool) : A m b ⟶ A (m + 1) b :=
  (I m b).inv ≫ ρ b ≫ (I (m + 1) b).hom

local notation "S" => arithmeticThreeDiagonalInitialRestriction hπ data H hj u hu m

/-- The full initial comparison is an exact square for the original quotient. -/
@[reassoc] theorem arithmeticThreeDiagonalInitialIso_restriction (b : Bool) :
    (I m b).hom ≫ S b = ρ b ≫ (I (m + 1) b).hom := by
  rw [arithmeticThreeDiagonalInitialRestriction, Iso.hom_inv_id_assoc]

/-- The whole corrected initial open has the coefficient map of its actual new smoothing. -/
@[reassoc] theorem arithmeticThreeDiagonalInitialNodeChart_restriction (b : Bool) :
    S b ≫ F (m + 1) b =
      F m b ≫ arithmeticThreeDiagonalInitialNodeRestriction hπ data H hj u hu m b := by
  apply (cancel_epi (I m b).hom).mp
  rw [← Category.assoc, arithmeticThreeDiagonalInitialIso_restriction,
    Category.assoc, arithmeticThreeFiniteInitialIso_nodeChart]
  rw [← Category.assoc, arithmeticFifthFartherNodeChart_restriction, Category.assoc]
  change (M m b ≫ arithmeticFifthFartherNodeRestriction hπ data H 3 hj u hu m b ≫
    (C (m + 1) b).hom) = _
  rw [arithmeticThreeDiagonalInitialNodeIso_restriction,
    ← arithmeticThreeFiniteInitialIso_nodeChart_assoc]

end FLT.Mazur.WeierstrassDividedDepth

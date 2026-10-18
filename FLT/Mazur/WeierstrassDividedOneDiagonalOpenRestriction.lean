/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneDiagonalNodeRestriction
public import FLT.Mazur.WeierstrassDividedFifthInitialOpenRestriction

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
  (H : ArithmeticAtlasCoefficients data) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "A" => fun l ↦ arithmeticOneFiniteInitialObject hπ data H l l hj u hu
local notation "I" => fun l ↦ arithmeticOneFiniteInitialIso hπ data H l l hj u hu
local notation "F" => fun l ↦ arithmeticOneFiniteInitialNodeChart hπ data H l l hj u hu
local notation "M" => fun k ↦ arithmeticFifthInitialNodeChart hπ data H k 1 hj u hu
local notation "C" => fun l ↦ arithmeticOneFiniteInitialNodeIso hπ data H l l hj u hu
local notation "ρ" => arithmeticFifthInitialOpenRestriction hπ data H 1 hj u hu m

/-- The full original coefficient map transported to the corrected initial opens. -/
def arithmeticOneDiagonalInitialRestriction (b : Bool) : A m b ⟶ A (m + 1) b :=
  (I m b).inv ≫ ρ b ≫ (I (m + 1) b).hom

local notation "S" => arithmeticOneDiagonalInitialRestriction hπ data H hj u hu m

/-- The full initial comparison is an exact square for the original quotient. -/
@[reassoc] theorem arithmeticOneDiagonalInitialIso_restriction (b : Bool) :
    (I m b).hom ≫ S b = ρ b ≫ (I (m + 1) b).hom := by
  rw [arithmeticOneDiagonalInitialRestriction, Iso.hom_inv_id_assoc]

/-- The whole corrected initial open has the coefficient map of its actual new smoothing. -/
@[reassoc] theorem arithmeticOneDiagonalInitialNodeChart_restriction (b : Bool) :
    S b ≫ F (m + 1) b =
      F m b ≫ arithmeticOneDiagonalInitialNodeRestriction hπ data H hj u hu m b := by
  apply (cancel_epi (I m b).hom).mp
  rw [← Category.assoc, arithmeticOneDiagonalInitialIso_restriction,
    Category.assoc, arithmeticOneFiniteInitialIso_nodeChart]
  rw [← Category.assoc, arithmeticFifthInitialNodeChart_restriction, Category.assoc]
  change (M m b ≫ arithmeticFifthInitialNodeRestriction hπ data H 1 hj u hu m b ≫
    (C (m + 1) b).hom) = _
  rw [arithmeticOneDiagonalInitialNodeIso_restriction,
    ← arithmeticOneFiniteInitialIso_nodeChart_assoc]

end FLT.Mazur.WeierstrassDividedDepth

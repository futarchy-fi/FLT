/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthInitialNodeRestriction
public import FLT.Mazur.WeierstrassDividedThirdInitialRestriction

/-!
# Quotient squares for the fourth corrected initial open

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
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "A" => fun k ↦ arithmeticFourthInitialObject hπ data H k j hj u hu
local notation "I" => fun k ↦ arithmeticFourthInitialIso hπ data H k j hj u hu
local notation "F" => fun k ↦ arithmeticFourthInitialNodeChart hπ data H k j hj u hu
local notation "M" => fun k ↦ arithmeticThirdInitialNodeChart hπ data H k j hj u hu
local notation "C" => fun k ↦ arithmeticFourthInitialNodeIso hπ data H k j hj u hu
local notation "ρ" => arithmeticThirdInitialRestriction hπ data H j hj u hu m

/-- The full original coefficient map transported to the corrected initial opens. -/
def arithmeticFourthInitialOpenRestriction (b : Bool) : A m b ⟶ A (m + 1) b :=
  (I m b).inv ≫ ρ b ≫ (I (m + 1) b).hom

local notation "S" => arithmeticFourthInitialOpenRestriction hπ data H j hj u hu m

/-- The full initial comparison is an exact square for the original quotient. -/
@[reassoc] theorem arithmeticFourthInitialIso_restriction (b : Bool) :
    (I m b).hom ≫ S b = ρ b ≫ (I (m + 1) b).hom := by
  rw [arithmeticFourthInitialOpenRestriction, Iso.hom_inv_id_assoc]

/-- The whole corrected initial open has the coefficient map of its actual new smoothing. -/
@[reassoc] theorem arithmeticFourthInitialNodeChart_restriction (b : Bool) :
    S b ≫ F (m + 1) b =
      F m b ≫ arithmeticFourthInitialNodeRestriction hπ data H j hj u hu m b := by
  apply (cancel_epi (I m b).hom).mp
  rw [← Category.assoc, arithmeticFourthInitialIso_restriction,
    Category.assoc, arithmeticFourthInitialIso_nodeChart]
  rw [← Category.assoc, arithmeticThirdInitialNodeChart_restriction, Category.assoc]
  change (M m b ≫ arithmeticThirdEarlierRestriction hπ data H j hj u hu m b ≫
    (C (m + 1) b).hom) = _
  rw [arithmeticFourthInitialNodeIso_restriction,
    ← arithmeticFourthInitialIso_nodeChart_assoc]

end FLT.Mazur.WeierstrassDividedDepth

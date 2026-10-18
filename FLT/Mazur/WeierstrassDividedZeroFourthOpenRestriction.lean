/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFourthNodeRestriction
public import FLT.Mazur.WeierstrassDividedZeroThirdOpenRestriction

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
local notation "A" => fun k ↦ arithmeticZeroFourthInitialObject hπ data H k j hj u hu
local notation "I" => fun k ↦ arithmeticZeroFourthInitialIso hπ data H k j hj u hu
local notation "F" => fun k ↦ arithmeticZeroFourthInitialNodeChart hπ data H k j hj u hu
local notation "M" => fun k ↦ arithmeticZeroThirdInitialNodeChart hπ data H k j hj u hu
local notation "C" => fun k ↦ arithmeticZeroFourthInitialNodeIso hπ data H k j hj u hu
local notation "ρ" => arithmeticZeroThirdInitialRestriction hπ data H j hj u hu m

/-- The full original coefficient map transported to the corrected initial opens. -/
def arithmeticZeroFourthInitialRestriction (b : Bool) : A m b ⟶ A (m + 1) b :=
  (I m b).inv ≫ ρ b ≫ (I (m + 1) b).hom

local notation "S" => arithmeticZeroFourthInitialRestriction hπ data H j hj u hu m

/-- The full initial comparison is an exact square for the original quotient. -/
@[reassoc] theorem arithmeticZeroFourthInitialIso_restriction (b : Bool) :
    (I m b).hom ≫ S b = ρ b ≫ (I (m + 1) b).hom := by
  rw [arithmeticZeroFourthInitialRestriction, Iso.hom_inv_id_assoc]

/-- The whole corrected initial open has the coefficient map of its actual new smoothing. -/
@[reassoc] theorem arithmeticZeroFourthInitialNodeChart_restriction (b : Bool) :
    S b ≫ F (m + 1) b =
      F m b ≫ arithmeticZeroFourthInitialNodeRestriction hπ data H j hj u hu m b := by
  apply (cancel_epi (I m b).hom).mp
  rw [← Category.assoc, arithmeticZeroFourthInitialIso_restriction,
    Category.assoc, arithmeticZeroFourthInitialIso_nodeChart]
  rw [← Category.assoc, arithmeticZeroThirdInitialNodeChart_restriction, Category.assoc]
  change (M m b ≫ arithmeticZeroThirdInitialNodeRestriction hπ data H j hj u hu m b ≫
    (C (m + 1) b).hom) = _
  rw [arithmeticZeroFourthInitialNodeIso_restriction,
    ← arithmeticZeroFourthInitialIso_nodeChart_assoc]

end FLT.Mazur.WeierstrassDividedDepth

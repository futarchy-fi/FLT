/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthInitialNodeRestriction
public import FLT.Mazur.WeierstrassDividedFourthInitialOpenRestriction

/-!
# Original quotient squares for the full corrected initial open

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
local notation "A" => fun k ↦ arithmeticFifthInitialObject hπ data H k j hj u hu
local notation "I" => fun k ↦ arithmeticFifthInitialIso hπ data H k j hj u hu
local notation "F" => fun k ↦ arithmeticFifthInitialNodeChart hπ data H k j hj u hu
local notation "M" => fun k ↦ arithmeticFourthInitialNodeChart hπ data H k j hj u hu
local notation "C" => fun k ↦ arithmeticFifthInitialNodeIso hπ data H k j hj u hu
local notation "ρ" => arithmeticFourthInitialOpenRestriction hπ data H j hj u hu m

/-- The full original coefficient map transported to the corrected initial opens. -/
def arithmeticFifthInitialOpenRestriction (b : Bool) : A m b ⟶ A (m + 1) b :=
  (I m b).inv ≫ ρ b ≫ (I (m + 1) b).hom

local notation "S" => arithmeticFifthInitialOpenRestriction hπ data H j hj u hu m

/-- The full initial comparison is an exact square for the original quotient. -/
@[reassoc] theorem arithmeticFifthInitialIso_restriction (b : Bool) :
    (I m b).hom ≫ S b = ρ b ≫ (I (m + 1) b).hom := by
  rw [arithmeticFifthInitialOpenRestriction, Iso.hom_inv_id_assoc]

/-- The whole corrected initial open has the coefficient map of its actual new smoothing. -/
@[reassoc] theorem arithmeticFifthInitialNodeChart_restriction (b : Bool) :
    S b ≫ F (m + 1) b =
      F m b ≫ arithmeticFifthInitialNodeRestriction hπ data H j hj u hu m b := by
  apply (cancel_epi (I m b).hom).mp
  rw [← Category.assoc, arithmeticFifthInitialIso_restriction,
    Category.assoc, arithmeticFifthInitialIso_nodeChart]
  rw [← Category.assoc, arithmeticFourthInitialNodeChart_restriction, Category.assoc]
  rw [arithmeticFifthInitialNodeIso_restriction,
    ← arithmeticFifthInitialIso_nodeChart_assoc]

/-- The transported initial puncture respects the original full Laurent coefficient quotient. -/
@[reassoc] theorem arithmeticFifthInitialPuncture_restriction (b : Bool) :
    arithmeticFifthInitialPuncture hπ data H m j hj u hu b ≫ S b =
      closingOverlapRestriction (R := R) (π := π) m ≫
        arithmeticFifthInitialPuncture hπ data H (m + 1) j hj u hu b := by
  apply (cancel_mono (F (m + 1) b)).mp
  rw [Category.assoc, arithmeticFifthInitialNodeChart_restriction, ← Category.assoc,
    arithmeticFifthInitialPuncture_nodeChart, Category.assoc,
    arithmeticFifthInitialPuncture_nodeChart]
  exact leftBranchOpen_ringMap (restriction R π m).toRingHom _ _
    (arithmeticFifthInitialSmoothing_restriction hπ data H j hj u hu m b)

end FLT.Mazur.WeierstrassDividedDepth

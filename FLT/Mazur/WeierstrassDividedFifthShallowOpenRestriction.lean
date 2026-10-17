/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowNodeRestriction
public import FLT.Mazur.WeierstrassDividedFourthShallowOpenRestriction

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
local notation "A" => fun k ↦ arithmeticFifthShallowObject hπ data H k j hj u hu
local notation "I" => fun k ↦ arithmeticFifthShallowIso hπ data H k j hj u hu
local notation "F" => fun k ↦ arithmeticFifthShallowNodeChart hπ data H k j hj u hu
local notation "M" => fun k ↦ arithmeticFourthShallowNodeChart hπ data H k j hj u hu
local notation "C" => fun k ↦ arithmeticFifthShallowNodeIso hπ data H k j hj u hu
local notation "ρ" => arithmeticFourthShallowOpenRestriction hπ data H j hj u hu m

/-- The full original coefficient map transported to the corrected initial opens. -/
def arithmeticFifthShallowOpenRestriction (b : Bool) : A m b ⟶ A (m + 1) b :=
  (I m b).inv ≫ ρ b ≫ (I (m + 1) b).hom

local notation "S" => arithmeticFifthShallowOpenRestriction hπ data H j hj u hu m

/-- The full initial comparison is an exact square for the original quotient. -/
@[reassoc] theorem arithmeticFifthShallowIso_restriction (b : Bool) :
    (I m b).hom ≫ S b = ρ b ≫ (I (m + 1) b).hom := by
  rw [arithmeticFifthShallowOpenRestriction, Iso.hom_inv_id_assoc]

/-- The whole corrected initial open has the coefficient map of its actual new smoothing. -/
@[reassoc] theorem arithmeticFifthShallowNodeChart_restriction (b : Bool) :
    S b ≫ F (m + 1) b =
      F m b ≫ arithmeticFifthShallowNodeRestriction hπ data H j hj u hu m b := by
  apply (cancel_epi (I m b).hom).mp
  rw [← Category.assoc, arithmeticFifthShallowIso_restriction,
    Category.assoc, arithmeticFifthShallowIso_nodeChart]
  rw [← Category.assoc, arithmeticFourthShallowNodeChart_restriction, Category.assoc]
  rw [arithmeticFifthShallowNodeIso_restriction,
    ← arithmeticFifthShallowIso_nodeChart_assoc]

/-- The transported initial puncture respects the original full Laurent coefficient quotient. -/
@[reassoc] theorem arithmeticFifthShallowPuncture_restriction (b : Bool) :
    arithmeticFifthShallowPuncture hπ data H m j hj u hu b ≫ S b =
      closingOverlapRestriction (R := R) (π := π) m ≫
        arithmeticFifthShallowPuncture hπ data H (m + 1) j hj u hu b := by
  apply (cancel_mono (F (m + 1) b)).mp
  rw [Category.assoc, arithmeticFifthShallowNodeChart_restriction, ← Category.assoc,
    arithmeticFifthShallowPuncture_nodeChart, Category.assoc,
    arithmeticFifthShallowPuncture_nodeChart]
  exact leftBranchOpen_ringMap (restriction R π m).toRingHom _ _
    (arithmeticFifthShallowSmoothing_restriction hπ data H j hj u hu m b)

end FLT.Mazur.WeierstrassDividedDepth

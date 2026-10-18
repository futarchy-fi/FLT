/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFirstGeometry
public import FLT.Mazur.WeierstrassDividedZeroFirstNodeRestriction

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
local notation "A" => fun k ↦ arithmeticZeroFirstInitialObject hπ data H k j hj u hu
local notation "I" => fun k ↦ arithmeticZeroFirstInitialIso hπ data H k j hj u hu
local notation "F" => fun k ↦ arithmeticZeroFirstInitialNodeChart hπ data H k j hj u hu
local notation "M" => fun k ↦ arithmeticInitialMobiusChart W H.a1_unit (π ^ 1) π k
local notation "C" => fun k ↦ arithmeticZeroFirstInitialNodeIso hπ data H k j hj u hu
local notation "ρ" => arithmeticFullInitialNodeQuotient R π m W (π ^ 1)

/-- The full original coefficient map transported to the corrected initial opens. -/
def arithmeticZeroFirstInitialRestriction (b : Bool) : A m b ⟶ A (m + 1) b :=
  (I m b).inv ≫ ρ ≫ (I (m + 1) b).hom

local notation "S" => arithmeticZeroFirstInitialRestriction hπ data H j hj u hu m

/-- The full initial comparison is an exact square for the original quotient. -/
@[reassoc] theorem arithmeticZeroFirstInitialIso_restriction (b : Bool) :
    (I m b).hom ≫ S b = ρ ≫ (I (m + 1) b).hom := by
  rw [arithmeticZeroFirstInitialRestriction, Iso.hom_inv_id_assoc]

/-- The whole corrected initial open has the coefficient map of its actual new smoothing. -/
@[reassoc] theorem arithmeticZeroFirstInitialNodeChart_restriction (b : Bool) :
    S b ≫ F (m + 1) b =
      F m b ≫ arithmeticZeroFirstInitialNodeRestriction hπ data H j hj u hu m b := by
  apply (cancel_epi (I m b).hom).mp
  rw [← Category.assoc, arithmeticZeroFirstInitialIso_restriction,
    Category.assoc, arithmeticZeroFirstInitialIso_nodeChart]
  rw [← Category.assoc, arithmeticInitialMobiusChart_restriction, Category.assoc]
  change (M m ≫ closingNormalizedRestriction data H m ≫ (C (m + 1) b).hom) = _
  rw [arithmeticZeroFirstInitialNodeIso_restriction,
    ← arithmeticZeroFirstInitialIso_nodeChart_assoc]

end FLT.Mazur.WeierstrassDividedDepth

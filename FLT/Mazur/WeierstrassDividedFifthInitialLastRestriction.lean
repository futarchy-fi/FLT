/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthInitialLastGeometry
public import FLT.Mazur.WeierstrassDividedFourthNodeRestriction

/-!
# Original coefficient squares for the fifth depth-one geometric factors

The last node retains its original normalized quotient and orientation.
Both fifth fields belong to the same whole-node coefficient square.
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
local notation "N" => closingNormalizedRestriction data H m
local notation "L" => fun k ↦ arithmeticFifthInitialLastIso hπ data H k j hj u hu
local notation "C" => fun k ↦ arithmeticFifthInitialLastOrientedIso hπ data H k j hj u hu
/-- The whole last-node correction respects the original normalized quotient. -/
@[reassoc] theorem arithmeticFifthInitialLastIso_restriction (b : Bool) :
    N ≫ (L (m + 1) b).hom = (L m b).hom ≫ N := by
  exact normalizedNodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticFifthInitialLastFactor_restriction hπ data H j hj u hu m b)
    _ _ (arithmeticFifthInitialLastSmoothing_pair hπ data H j hj u hu (m + 1) b)
    (arithmeticFifthInitialLastSmoothing_pair hπ data H j hj u hu m b)
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)

/-- The last label retains its orientation and the full coefficient square. -/
@[reassoc] theorem arithmeticFifthInitialLastOrientedIso_restriction (b : Bool) :
    N ≫ (C (m + 1) b).hom = (C m b).hom ≫ N := by
  simp only [arithmeticFifthInitialLastOrientedIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, twistedRetainedOrientation_inv_restriction,
    Category.assoc, ← Category.assoc N, arithmeticFifthInitialLastIso_restriction,
    Category.assoc, twistedRetainedOrientation_restriction]
  simp only [Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth

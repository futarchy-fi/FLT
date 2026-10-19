/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclicGlobalIso
public import FLT.Mazur.WeierstrassDividedZeroCyclicSourceRestriction

/-!
# The global five-gon isomorphism commutes with the actual quotients

Naturality is proved on all five entire source nodes using the full seed
coefficient arrows and their constructed diagonal comparison squares.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "F" => fun k ↦ arithmeticZeroCyclicGlobalIso hπ data H k hj u hu
local notation "c" => fun k ↦ arithmeticZeroCyclicSourceChart hπ data H k hj u hu
local notation "r" => arithmeticZeroCyclicSourceNodeRestriction hπ data H m hj u hu
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H m 0 hj u hu
local notation "v" => arithmeticZeroCyclicStandardRestriction hπ data H hj u hu m

/-- The entire scheme isomorphism follows the actual original and standard quotient arrows. -/
@[reassoc] theorem arithmeticZeroCyclicGlobalIso_restriction :
    q ≫ (F (m + 1)).hom = (F m).hom ≫ v := by
  apply arithmeticZeroCyclicSourceChart_hom_ext hπ data H m hj u hu
  intro i
  obtain ⟨j, rfl⟩ := zeroCyclicIndex.surjective i
  rw [arithmeticZeroCyclicSourceChart_restriction_assoc,
    arithmeticZeroCyclicGlobalIso_chart, arithmeticZeroCyclicGlobalIso_chart_assoc,
    arithmeticZeroCyclicStandardChart_restriction]
  dsimp only [arithmeticZeroCyclicSourceNodeRestriction, arithmeticZeroCyclicStandardParameter]
  rw [arithmeticZeroCyclicNodeIso_restriction_assoc]

/-- The inverse whole comparison also commutes with the actual original quotient arrows. -/
@[reassoc] theorem arithmeticZeroCyclicGlobalIso_inv_restriction :
    v ≫ (F (m + 1)).inv = (F m).inv ≫ q := by
  apply (cancel_epi (F m).hom).mp
  rw [← arithmeticZeroCyclicGlobalIso_restriction_assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclicSourceCharts
public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedFullRestriction

/-!
# The entire original cyclic initial charts commute with quotient

Transport the full pair quotient through the proved union isomorphism. This
keeps the actual original global restriction on both entire initial nodes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticZeroInfinityNormalizedFullComparison
  simultaneousTwistedArithmeticRestriction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "U" => fun k ↦ arithmeticZeroInfinityNormalizedFullUnion hπ data H k hj u hu
local notation "F" => fun k ↦ arithmeticZeroInfinityNormalizedFullComparison hπ data H k hj u hu
local notation "a" => fun k ↦ arithmeticZeroCyclicInitialChart hπ data H k hj u hu
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H m 0 hj u hu
local notation "ρ" => arithmeticZeroInfinityNormalizedFullUnionRestriction hπ data H m hj u hu
local notation "v" => arithmeticZeroInfinityNormalizedTargetRestriction data H m

/-- The inverse full union comparison commutes with the original global quotient. -/
@[reassoc] theorem arithmeticZeroCyclicInitialInverse_restriction :
    (F m).inv ≫ (U m).ι ≫ q = v ≫ (F (m + 1)).inv ≫ (U (m + 1)).ι := by
  apply (cancel_epi (F m).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← arithmeticZeroInfinityNormalizedFullComparison_restriction_assoc,
    Iso.hom_inv_id_assoc, arithmeticZeroInfinityNormalizedFullUnionRestriction_global]

/-- Both entire unreflected initial nodes have their original full coefficient square. -/
@[reassoc] theorem arithmeticZeroCyclicInitialChart_restriction (b : Bool) :
    a m b ≫ q = closingNormalizedRestriction data H m ≫ a (m + 1) b := by
  cases b <;> simp only [arithmeticZeroCyclicInitialChart, Bool.false_eq_true,
    ↓reduceIte, Category.assoc, arithmeticZeroCyclicInitialInverse_restriction]
  · rw [arithmeticZeroInfinityNormalizedTargetRestriction_first_assoc]
  · rw [arithmeticZeroInfinityNormalizedTargetRestriction_opposite_assoc]

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneRetainedCoefficientBase
public import FLT.Mazur.WeierstrassDividedOneInfinityNormalizedRetainedRestriction

/-!
# The true full retained-0 edge commutes with the actual node quotient

The exact original Laurent substitution follows the full source quotient.
The square is proved from global inclusions and the constructed pair comparison.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticOneFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticOneFiniteAtlasIso
  arithmeticOneDiagonalAtlasChart simultaneousTwistedArithmeticRestriction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => fun k ↦ Quotient R π k
local notation "D" => arithmeticOneDiagonalState hπ data H hj u hu
local notation "s" => fun m b ↦ PolygonArithmeticRetainedChain.State.retained D m 0 b
local notation "K" => fun k ↦
  arithmeticOneInfinityNormalizedRetainedParameter hπ data H k hj u hu
local notation "U" => fun k ↦ arithmeticOneInfinityNormalizedFullUnion hπ data H k hj u hu
local notation "w" => fun k ↦
  arithmeticOneInfinityNormalizedRetainedToUnion hπ data H k hj u hu
local notation "c" => fun k ↦ arithmeticOneDiagonalAtlasChart hπ data H k hj u hu
local notation "r" => fun k ↦ arithmeticOneInfinityNormalizedRetainedSide hπ data H k hj u hu
local notation "S" => arithmeticOneDiagonalAtlasRestriction hπ data H hj u hu m
local notation "ρ" => closingOverlapRestriction (R := R) (π := π) m

/-- The full retained-side parameter follows the actual corrected whole-node quotient. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedRetainedSide_restriction (b : Bool) :
    r m b ≫ S (.retained ⟨0, by omega⟩ b) = ρ ≫ r (m + 1) b := by
  apply (cancel_mono (c (m + 1) (.retained ⟨0, by omega⟩ b))).mp
  let q := simultaneousTwistedArithmeticRestriction hπ data H m 1 hj u hu
  let t := arithmeticOneInfinityNormalizedFullUnionRestriction hπ data H m hj u hu
  calc
    (r m b ≫ S (.retained ⟨0, by omega⟩ b)) ≫ c (m + 1) (.retained ⟨0, by omega⟩ b) =
        (r m b ≫ c m (.retained ⟨0, by omega⟩ b)) ≫ q := by
      rw [Category.assoc, arithmeticOneDiagonalAtlasChart_restriction, Category.assoc]
    _ = (w m b ≫ (U m).ι) ≫ q := congrArg (· ≫ q)
      (arithmeticOneInfinityNormalizedRetainedSide_global hπ data H m hj u hu b)
    _ = (w m b ≫ t) ≫ (U (m + 1)).ι := by
      simpa only [Category.assoc] using congrArg (w m b ≫ ·)
        (arithmeticOneInfinityNormalizedFullUnionRestriction_global hπ data H m hj u hu).symm
    _ = (ρ ≫ w (m + 1) b) ≫ (U (m + 1)).ι := congrArg (· ≫ (U (m + 1)).ι)
      (arithmeticOneInfinityNormalizedRetainedToUnion_restriction hπ data H m hj u hu b)
    _ = (ρ ≫ r (m + 1) b) ≫ c (m + 1) (.retained ⟨0, by omega⟩ b) := by
      simpa only [Category.assoc] using congrArg (ρ ≫ ·)
        (arithmeticOneInfinityNormalizedRetainedSide_global hπ data H (m + 1) hj u hu b).symm

/-- The same complete edge square uses the explicit retained-0 smoothing coefficient map. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedRetainedSide_nodeRestriction (b : Bool) :
    r m b ≫ arithmeticOneDiagonalRetainedRestriction hπ data H hj u hu m 0 b =
      ρ ≫ r (m + 1) b := by
  rw [← arithmeticOneDiagonalAtlasRestriction_first]
  exact arithmeticOneInfinityNormalizedRetainedSide_restriction hπ data H m hj u hu b

end FLT.Mazur.WeierstrassDividedDepth

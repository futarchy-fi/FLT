/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedPairRestriction
public import FLT.Mazur.WeierstrassDividedZeroDiagonalClosingBaseSystem

/-!
# The actual original three-chart union follows the global arithmetic quotient

Restrict the original global arrow to the full source union. Its comparison
commutes with the independent two-node target and keeps the original base.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticZeroFiniteAtlasIso
  arithmeticZeroFiniteAtlasChart simultaneousTwistedArithmeticRestriction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "c" => fun k ↦ arithmeticZeroDiagonalAtlasChart hπ data H k hj u hu
local notation "S" => arithmeticZeroDiagonalAtlasRestriction hπ data H hj u hu m
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H m 0 hj u hu
local notation "U" => fun k ↦ arithmeticZeroInfinityNormalizedFullUnion hπ data H k hj u hu
local notation "J" => fun k ↦ arithmeticZeroInfinityNormalizedFullUnionIso hπ data H k hj u hu
local notation "F" => fun k ↦ arithmeticZeroInfinityNormalizedFullComparison hπ data H k hj u hu
local notation "G" => fun k ↦ arithmeticZeroInfinityNormalizedPairIso hπ data H k hj u hu
local notation "B" => fun k ↦ arithmeticZeroDiagonalSourceToBase hπ data H k hj u hu
local notation "v" => arithmeticZeroInfinityNormalizedPairRestriction hπ data H m hj u hu
local notation "t" => arithmeticZeroInfinityNormalizedTargetRestriction data H m

/-- Each full source node union remains in the corresponding union under quotient. -/
theorem arithmeticZeroInfinityNormalizedUnion_restriction_le (b : Bool) :
    arithmeticZeroInfinityNormalizedUnion hπ data H m hj u hu b ≤
      q ⁻¹ᵁ arithmeticZeroInfinityNormalizedUnion hπ data H (m + 1) hj u hu b :=
  openPair_quotient_le (c m .infinity) (c m (.initial b))
    (c (m + 1) .infinity) (c (m + 1) (.initial b)) q (S .infinity) (S (.initial b))
    (arithmeticZeroDiagonalAtlasChart_restriction hπ data H hj u hu m .infinity)
    (arithmeticZeroDiagonalAtlasChart_restriction hπ data H hj u hu m (.initial b))

attribute [local irreducible] arithmeticZeroInfinityNormalizedUnion

/-- The original global quotient preserves the entire original three-chart union. -/
theorem arithmeticZeroInfinityNormalizedFullUnion_restriction_le :
    U m ≤ q ⁻¹ᵁ U (m + 1) := by
  simp only [arithmeticZeroInfinityNormalizedFullUnion, Scheme.Hom.preimage_sup]
  exact sup_le_sup
    (arithmeticZeroInfinityNormalizedUnion_restriction_le hπ data H m hj u hu false)
    (arithmeticZeroInfinityNormalizedUnion_restriction_le hπ data H m hj u hu true)

/-- Restrict the actual global quotient to its full original initial/infinity union. -/
def arithmeticZeroInfinityNormalizedFullUnionRestriction :
    (U m).toScheme ⟶ (U (m + 1)).toScheme :=
  (q).resLE _ _ (arithmeticZeroInfinityNormalizedFullUnion_restriction_le hπ data H m hj u hu)

local notation "ρ" => arithmeticZeroInfinityNormalizedFullUnionRestriction hπ data H m hj u hu

/-- The whole source union keeps the original global quotient arrow. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedFullUnionRestriction_global :
    ρ ≫ (U (m + 1)).ι = (U m).ι ≫ q := Scheme.Hom.resLE_comp_ι _ _

/-- The actual union and its complete pair presentation have the same quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedFullUnionIso_restriction :
    (J m).hom ≫ ρ = v ≫ (J (m + 1)).hom := by
  apply (cancel_mono (U (m + 1)).ι).mp
  simp only [Category.assoc, arithmeticZeroInfinityNormalizedFullUnionRestriction_global,
    arithmeticZeroInfinityNormalizedFullUnionIso_global,
    arithmeticZeroInfinityNormalizedFullUnionIso_global_assoc,
    arithmeticZeroInfinityNormalizedPairRestriction_global]

/-- The complete original three-chart comparison follows the independent target quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedFullComparison_restriction :
    ρ ≫ (F (m + 1)).hom = (F m).hom ≫ t := by
  apply (cancel_epi (J m).hom).mp
  rw [arithmeticZeroInfinityNormalizedFullUnionIso_restriction_assoc,
    arithmeticZeroInfinityNormalizedFullComparison_transport,
    arithmeticZeroInfinityNormalizedFullComparison_transport_assoc,
    arithmeticZeroInfinityNormalizedPairIso_restriction]

/-- The entire original union retains the original coefficient quotient square. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedFullUnionRestriction_base :
    ρ ≫ (U (m + 1)).ι ≫ B (m + 1) =
      (U m).ι ≫ B m ≫ baseRestriction R π m := by
  rw [arithmeticZeroInfinityNormalizedFullUnionRestriction_global_assoc,
    arithmeticZeroDiagonalSourceToBase_restriction]

include hπ hj u hu in
/-- The independent two-node quotient retains the original coefficient base. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedTargetRestriction_base :
    t ≫ arithmeticZeroInfinityNormalizedTargetToBase data H (m + 1) =
      arithmeticZeroInfinityNormalizedTargetToBase data H m ≫ baseRestriction R π m := by
  apply (cancel_epi (F m).hom).mp
  rw [← arithmeticZeroInfinityNormalizedFullComparison_restriction_assoc,
    arithmeticZeroInfinityNormalizedFullComparison_base,
    arithmeticZeroInfinityNormalizedFullComparison_base_assoc,
    arithmeticZeroInfinityNormalizedFullUnionRestriction_base]

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInfinityNormalizedPairRestriction
public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedFullRestriction

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
  arithmeticOneFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticOneFiniteAtlasIso
  arithmeticOneFiniteAtlasChart simultaneousTwistedArithmeticRestriction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "c" => fun k ↦ arithmeticOneDiagonalAtlasChart hπ data H k hj u hu
local notation "S" => arithmeticOneDiagonalAtlasRestriction hπ data H hj u hu m
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H m 1 hj u hu
local notation "U" => fun k ↦ arithmeticOneInfinityNormalizedFullUnion hπ data H k hj u hu
local notation "J" => fun k ↦ arithmeticOneInfinityNormalizedFullUnionIso hπ data H k hj u hu
local notation "F" => fun k ↦ arithmeticOneInfinityNormalizedFullComparison hπ data H k hj u hu
local notation "G" => fun k ↦ arithmeticOneInfinityNormalizedPairIso hπ data H k hj u hu
local notation "B" => fun k ↦ arithmeticOneDiagonalSourceToBase hπ data H k hj u hu
local notation "v" => arithmeticOneInfinityNormalizedPairRestriction hπ data H m hj u hu
local notation "t" => arithmeticOneInfinityNormalizedTargetRestriction data H m

/-- The entire original source retains its exact coefficient quotient arrow. -/
@[reassoc] theorem arithmeticOneDiagonalSourceToBase_restriction :
    q ≫ B (m + 1) = B m ≫ baseRestriction R π m := by
  simp only [simultaneousTwistedArithmeticRestriction, arithmeticOneDiagonalSourceToBase,
    Category.assoc, Iso.hom_inv_id_assoc, finiteGlobalArithmeticRestriction_structure]

/-- Each full source node union remains in the corresponding union under quotient. -/
theorem arithmeticOneInfinityNormalizedUnion_restriction_le (b : Bool) :
    arithmeticOneInfinityNormalizedUnion hπ data H m hj u hu b ≤
      q ⁻¹ᵁ arithmeticOneInfinityNormalizedUnion hπ data H (m + 1) hj u hu b :=
  openPair_quotient_le (c m .infinity) (c m (.initial b))
    (c (m + 1) .infinity) (c (m + 1) (.initial b)) q (S .infinity) (S (.initial b))
    (arithmeticOneDiagonalAtlasChart_restriction hπ data H hj u hu m .infinity)
    (arithmeticOneDiagonalAtlasChart_restriction hπ data H hj u hu m (.initial b))

attribute [local irreducible] arithmeticOneInfinityNormalizedUnion

/-- The original global quotient preserves the entire original three-chart union. -/
theorem arithmeticOneInfinityNormalizedFullUnion_restriction_le :
    U m ≤ q ⁻¹ᵁ U (m + 1) := by
  simp only [arithmeticOneInfinityNormalizedFullUnion, Scheme.Hom.preimage_sup]
  exact sup_le_sup
    (arithmeticOneInfinityNormalizedUnion_restriction_le hπ data H m hj u hu false)
    (arithmeticOneInfinityNormalizedUnion_restriction_le hπ data H m hj u hu true)

/-- Restrict the actual global quotient to its full original initial/infinity union. -/
def arithmeticOneInfinityNormalizedFullUnionRestriction :
    (U m).toScheme ⟶ (U (m + 1)).toScheme :=
  (q).resLE _ _ (arithmeticOneInfinityNormalizedFullUnion_restriction_le hπ data H m hj u hu)

local notation "ρ" => arithmeticOneInfinityNormalizedFullUnionRestriction hπ data H m hj u hu

/-- The whole source union keeps the original global quotient arrow. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedFullUnionRestriction_global :
    ρ ≫ (U (m + 1)).ι = (U m).ι ≫ q := Scheme.Hom.resLE_comp_ι _ _

/-- The actual union and its complete pair presentation have the same quotient. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedFullUnionIso_restriction :
    (J m).hom ≫ ρ = v ≫ (J (m + 1)).hom := by
  apply (cancel_mono (U (m + 1)).ι).mp
  simp only [Category.assoc, arithmeticOneInfinityNormalizedFullUnionRestriction_global,
    arithmeticOneInfinityNormalizedFullUnionIso_global,
    arithmeticOneInfinityNormalizedFullUnionIso_global_assoc,
    arithmeticOneInfinityNormalizedPairRestriction_global]

/-- The complete original three-chart comparison follows the independent target quotient. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedFullComparison_restriction :
    ρ ≫ (F (m + 1)).hom = (F m).hom ≫ t := by
  apply (cancel_epi (J m).hom).mp
  rw [arithmeticOneInfinityNormalizedFullUnionIso_restriction_assoc,
    arithmeticOneInfinityNormalizedFullComparison_transport,
    arithmeticOneInfinityNormalizedFullComparison_transport_assoc,
    arithmeticOneInfinityNormalizedPairIso_restriction]

/-- The entire original union retains the original coefficient quotient square. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedFullUnionRestriction_base :
    ρ ≫ (U (m + 1)).ι ≫ B (m + 1) =
      (U m).ι ≫ B m ≫ baseRestriction R π m := by
  rw [arithmeticOneInfinityNormalizedFullUnionRestriction_global_assoc,
    arithmeticOneDiagonalSourceToBase_restriction]

include hπ hj u hu in
/-- The independent two-node quotient retains the original coefficient base. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedTargetRestriction_base :
    t ≫ arithmeticOneInfinityNormalizedTargetToBase data H (m + 1) =
      arithmeticOneInfinityNormalizedTargetToBase data H m ≫ baseRestriction R π m := by
  apply (cancel_epi (F m).hom).mp
  rw [← arithmeticOneInfinityNormalizedFullComparison_restriction_assoc,
    arithmeticOneInfinityNormalizedFullComparison_base,
    arithmeticOneInfinityNormalizedFullComparison_base_assoc,
    arithmeticOneInfinityNormalizedFullUnionRestriction_base]

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedRetainedPairQuotient

/-!
# The entire original retained union under the actual global quotient

Restrict the original global map to the whole five-chart union. The extended
comparison follows the independently glued target map and the original base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteAtlasIso simultaneousTwistedArithmeticIso
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
  arithmeticZeroDiagonalAtlasChart simultaneousTwistedArithmeticRestriction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "V" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedPairUnion hπ data H k hj u hu
local notation "J" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedPairUnionIso hπ data H k hj u hu
local notation "F" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedPairComparison hπ data H k hj u hu
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H m 0 hj u hu
local notation "d" =>
  arithmeticZeroInfinityNormalizedRetainedPairPushoutRestriction hπ data H m hj u hu
local notation "t" =>
  arithmeticZeroInfinityNormalizedRetainedPairTargetRestriction hπ data H m hj u hu
local notation "B" => fun k ↦ arithmeticZeroDiagonalSourceToBase hπ data H k hj u hu
local notation "p" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedPairTargetToBase hπ data H k hj u hu

/-- The entire five-chart source union is preserved by the original arithmetic quotient. -/
theorem arithmeticZeroInfinityNormalizedRetainedPairUnion_restriction_le :
    V m ≤ q ⁻¹ᵁ V (m + 1) := by
  apply sup_le
  · exact le_trans
      (arithmeticZeroInfinityNormalizedRetainedUnion_restriction_le hπ data H m hj u hu false)
      ((q).preimage_mono le_sup_left)
  · exact le_trans
      (arithmeticZeroInfinityNormalizedRetainedUnion_restriction_le hπ data H m hj u hu true)
      ((q).preimage_mono le_sup_right)

/-- The actual full source union carries the restriction of its original global quotient. -/
def arithmeticZeroInfinityNormalizedRetainedPairUnionRestriction :
    (V m).toScheme ⟶ (V (m + 1)).toScheme :=
  (q).resLE _ _
    (arithmeticZeroInfinityNormalizedRetainedPairUnion_restriction_le hπ data H m hj u hu)

local notation "ρ" =>
  arithmeticZeroInfinityNormalizedRetainedPairUnionRestriction hπ data H m hj u hu

/-- The entire actual union quotient preserves the original global arrow. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPairUnionRestriction_global :
    ρ ≫ (V (m + 1)).ι = (V m).ι ≫ q := Scheme.Hom.resLE_comp_ι _ _

/-- The full union presentation has the same actual quotient as its source pushout. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPairUnionIso_restriction :
    (J m).hom ≫ ρ = d ≫ (J (m + 1)).hom := by
  apply (cancel_mono (V (m + 1)).ι).mp
  simp only [Category.assoc, arithmeticZeroInfinityNormalizedRetainedPairUnionRestriction_global,
    arithmeticZeroInfinityNormalizedRetainedPairUnionIso_global,
    arithmeticZeroInfinityNormalizedRetainedPairUnionIso_global_assoc,
    arithmeticZeroInfinityNormalizedRetainedPairPushoutRestriction_global]

/-- The complete attached comparison follows the independently glued full quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPairComparison_restriction :
    ρ ≫ (F (m + 1)).hom = (F m).hom ≫ t := by
  apply (cancel_epi (J m).hom).mp
  rw [arithmeticZeroInfinityNormalizedRetainedPairUnionIso_restriction_assoc]
  simp only [arithmeticZeroInfinityNormalizedRetainedPairComparison, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc,
    arithmeticZeroInfinityNormalizedRetainedPairPushoutRestriction_comparison]

/-- The entire original union retains the original coefficient quotient square. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPairUnionRestriction_base :
    ρ ≫ (V (m + 1)).ι ≫ B (m + 1) =
      (V m).ι ≫ B m ≫ baseRestriction R π m := by
  rw [arithmeticZeroInfinityNormalizedRetainedPairUnionRestriction_global_assoc,
    arithmeticZeroDiagonalSourceToBase_restriction]

/-- The independent full target quotient retains the original base square. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPairTargetRestriction_base :
    t ≫ p (m + 1) = p m ≫ baseRestriction R π m := by
  apply (cancel_epi (F m).hom).mp
  rw [← arithmeticZeroInfinityNormalizedRetainedPairComparison_restriction_assoc,
    arithmeticZeroInfinityNormalizedRetainedPairComparison_base,
    arithmeticZeroInfinityNormalizedRetainedPairComparison_base_assoc,
    arithmeticZeroInfinityNormalizedRetainedPairUnionRestriction_base]

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedRetainedQuotient

/-!
# The entire original retained union under the actual global quotient

Restrict the original global map to the whole four-chart union. The extended
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
local notation "U" => fun k ↦ arithmeticZeroInfinityNormalizedFullUnion hπ data H k hj u hu
local notation "V" => fun k ↦ arithmeticZeroInfinityNormalizedRetainedUnion hπ data H k hj u hu
local notation "J" => fun k ↦ arithmeticZeroInfinityNormalizedRetainedUnionIso hπ data H k hj u hu
local notation "F" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedComparison hπ data H k hj u hu
local notation "G" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedPushoutIso hπ data H k hj u hu
local notation "c" => fun k ↦ arithmeticZeroDiagonalAtlasChart hπ data H k hj u hu
local notation "S" => arithmeticZeroDiagonalAtlasRestriction hπ data H hj u hu m
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H m 0 hj u hu
local notation "a" => arithmeticZeroInfinityNormalizedFullUnionRestriction hπ data H m hj u hu
local notation "d" =>
  arithmeticZeroInfinityNormalizedRetainedPushoutRestriction hπ data H m hj u hu
local notation "t" => arithmeticZeroInfinityNormalizedRetainedTargetRestriction hπ data H m hj u hu
local notation "B" => fun k ↦ arithmeticZeroDiagonalSourceToBase hπ data H k hj u hu
local notation "p" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedTargetToBase hπ data H k hj u hu

/-- The entire four-chart source union is preserved by the original arithmetic quotient. -/
theorem arithmeticZeroInfinityNormalizedRetainedUnion_restriction_le (b : Bool) :
    V m b ≤ q ⁻¹ᵁ V (m + 1) b := by
  simpa only [arithmeticZeroInfinityNormalizedRetainedUnion, Scheme.Opens.opensRange_ι] using
    openPair_quotient_le (U m).ι (c m (.retained ⟨0, by omega⟩ b))
      (U (m + 1)).ι (c (m + 1) (.retained ⟨0, by omega⟩ b))
      q a (S (.retained ⟨0, by omega⟩ b))
      (arithmeticZeroInfinityNormalizedFullUnionRestriction_global hπ data H m hj u hu)
      (arithmeticZeroDiagonalAtlasChart_restriction hπ data H hj u hu m _)

/-- The actual full source union carries the restriction of its original global quotient. -/
def arithmeticZeroInfinityNormalizedRetainedUnionRestriction (b : Bool) :
    (V m b).toScheme ⟶ (V (m + 1) b).toScheme :=
  (q).resLE _ _
    (arithmeticZeroInfinityNormalizedRetainedUnion_restriction_le hπ data H m hj u hu b)

local notation "ρ" =>
  arithmeticZeroInfinityNormalizedRetainedUnionRestriction hπ data H m hj u hu

/-- The entire actual union quotient preserves the original global arrow. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedUnionRestriction_global (b : Bool) :
    ρ b ≫ (V (m + 1) b).ι = (V m b).ι ≫ q := Scheme.Hom.resLE_comp_ι _ _

/-- The full union presentation has the same actual quotient as its source pushout. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedUnionIso_restriction (b : Bool) :
    (J m b).hom ≫ ρ b = d b ≫ (J (m + 1) b).hom := by
  apply (cancel_mono (V (m + 1) b).ι).mp
  simp only [Category.assoc, arithmeticZeroInfinityNormalizedRetainedUnionRestriction_global,
    arithmeticZeroInfinityNormalizedRetainedUnionIso_global,
    arithmeticZeroInfinityNormalizedRetainedUnionIso_global_assoc,
    arithmeticZeroInfinityNormalizedRetainedPushoutRestriction_global]

/-- The complete attached comparison follows the independently glued full quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedComparison_restriction (b : Bool) :
    ρ b ≫ (F (m + 1) b).hom = (F m b).hom ≫ t b := by
  apply (cancel_epi (J m b).hom).mp
  rw [arithmeticZeroInfinityNormalizedRetainedUnionIso_restriction_assoc]
  simp only [arithmeticZeroInfinityNormalizedRetainedComparison, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc,
    arithmeticZeroInfinityNormalizedRetainedPushoutRestriction_comparison]

/-- The entire original union retains the original coefficient quotient square. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedUnionRestriction_base (b : Bool) :
    ρ b ≫ (V (m + 1) b).ι ≫ B (m + 1) =
      (V m b).ι ≫ B m ≫ baseRestriction R π m := by
  rw [arithmeticZeroInfinityNormalizedRetainedUnionRestriction_global_assoc,
    arithmeticZeroDiagonalSourceToBase_restriction]

/-- The independent full target quotient retains the original base square. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedTargetRestriction_base (b : Bool) :
    t b ≫ p (m + 1) b = p m b ≫ baseRestriction R π m := by
  apply (cancel_epi (F m b).hom).mp
  rw [← arithmeticZeroInfinityNormalizedRetainedComparison_restriction_assoc,
    arithmeticZeroInfinityNormalizedRetainedComparison_base,
    arithmeticZeroInfinityNormalizedRetainedComparison_base_assoc,
    arithmeticZeroInfinityNormalizedRetainedUnionRestriction_base]

end FLT.Mazur.WeierstrassDividedDepth

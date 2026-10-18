/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedBase

/-!
# The independent normalized pair and its full comparison over the original base

Glue the two node coefficient projections along the reciprocal right boundary.
The actual three-chart union comparison preserves this full coefficient map.
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
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "r" => rightBranchOpen Q τ
local notation "r'" => Iso.hom (edgeInversion Q) ≫ r
local notation "Z" => arithmeticZeroInfinityNormalizedTargetPair data H m
local notation "G" => arithmeticZeroInfinityNormalizedPairIso hπ data H m hj u hu
local notation "k" => arithmeticZeroInfinityNormalizedPairToGlobal hπ data H m hj u hu
local notation "q" => arithmeticZeroDiagonalSourceToBase hπ data H m hj u hu
local notation "U" => arithmeticZeroInfinityNormalizedFullUnion hπ data H m hj u hu
local notation "J" => arithmeticZeroInfinityNormalizedFullUnionIso hπ data H m hj u hu
local notation "F" => arithmeticZeroInfinityNormalizedFullComparison hπ data H m hj u hu

/-- The independent pair has its coefficient map on both entire nodes. -/
def arithmeticZeroInfinityNormalizedTargetToBase : Z ⟶ Spec (.of Q) :=
  pushout.desc (chartStructure Q τ) (chartStructure Q τ) (by
    rw [Category.assoc, rightBranchOpen_base, edgeInversion_base])

local notation "p" => arithmeticZeroInfinityNormalizedTargetToBase data H m

omit [IsDomain R] [IsBezout R] in
/-- The first complete target node has the original quotient coefficients. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedTargetToBase_first :
    pushout.inl r r' ≫ p = chartStructure Q τ := pushout.inl_desc _ _ _

omit [IsDomain R] [IsBezout R] in
/-- The opposite complete target node has the same original quotient coefficients. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedTargetToBase_opposite :
    pushout.inr r r' ≫ p = chartStructure Q τ := pushout.inr_desc _ _ _

/-- The full pair presentation preserves the original global arithmetic coefficient map. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedPairIso_base :
    (G).hom ≫ p = k ≫ q := by
  apply pushout.hom_ext
  · rw [arithmeticZeroInfinityNormalizedPairIso_first_assoc,
      arithmeticZeroInfinityNormalizedTargetToBase_first,
      arithmeticZeroInfinityNormalizedNodeIso_base,
      arithmeticZeroInfinityNormalizedPairToGlobal_first_assoc]
  · rw [arithmeticZeroInfinityNormalizedPairIso_opposite_assoc,
      arithmeticZeroInfinityNormalizedTargetToBase_opposite,
      arithmeticZeroInfinityNormalizedNodeIso_base,
      arithmeticZeroInfinityNormalizedPairToGlobal_opposite_assoc]

/-- Every point of the actual original three-chart comparison lies over the full base. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedFullComparison_base :
    (F).hom ≫ p = (U).ι ≫ q := by
  apply (cancel_epi (J).hom).mp
  rw [arithmeticZeroInfinityNormalizedFullComparison_transport_assoc,
    arithmeticZeroInfinityNormalizedPairIso_base,
    arithmeticZeroInfinityNormalizedFullUnionIso_global_assoc]

/-- The complete comparison is an isomorphism over the original quotient coefficient scheme. -/
def arithmeticZeroInfinityNormalizedFullComparisonOver :
    Over.mk ((U).ι ≫ q) ≅ Over.mk p :=
  Over.isoMk F (arithmeticZeroInfinityNormalizedFullComparison_base hπ data H m hj u hu)

end FLT.Mazur.WeierstrassDividedDepth

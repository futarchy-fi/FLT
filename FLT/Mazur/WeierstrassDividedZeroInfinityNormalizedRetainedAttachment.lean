/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedSystem

/-!
# Exact retained attachments on the full normalized source union

The complete original retained edge lands in the new target with its full K
parameter. Reparameterizing this edge exposes the precise required retained
node boundary, while preserving the constructed common infinity gluing.
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
local notation "i" => arithmeticZeroDiagonalOverlapToInfinity hπ data H m hj u hu
local notation "l" => arithmeticZeroDiagonalInitialOverlap hπ data H m hj u hu
local notation "a" => fun b ↦ pushout.inl i (l b)
local notation "c" => arithmeticZeroDiagonalAtlasChart hπ data H m hj u hu
local notation "A" => arithmeticZeroFiniteAtlasObject hπ data H m m hj u hu
local notation "U" => arithmeticZeroInfinityNormalizedFullUnion hπ data H m hj u hu
local notation "J" => arithmeticZeroInfinityNormalizedFullUnionIso hπ data H m hj u hu
local notation "F" => arithmeticZeroInfinityNormalizedFullComparison hπ data H m hj u hu
local notation "P" => arithmeticZeroFiniteInitialPuncture hπ data H m m 0 hj u hu
local notation "K" => arithmeticZeroInfinityNormalizedRetainedParameter hπ data H m hj u hu
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu

/-- Each full original initial chart enters the actual three-chart open union. -/
def arithmeticZeroInfinityNormalizedInitialToUnion (b : Bool) :
    A (.initial b) ⟶ (U).toScheme := by
  cases b
  · exact pushout.inr i (l false) ≫ pushout.inl (a false) (a true) ≫ (J).hom
  · exact pushout.inr i (l true) ≫ pushout.inr (a false) (a true) ≫ (J).hom

local notation "j" => arithmeticZeroInfinityNormalizedInitialToUnion hπ data H m hj u hu

instance arithmeticZeroInfinityNormalizedInitialToUnion_isOpenImmersion (b : Bool) :
    IsOpenImmersion (j b) := by
  cases b <;> dsimp only [arithmeticZeroInfinityNormalizedInitialToUnion] <;> infer_instance

/-- The full initial source map retains its actual global inclusion. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedInitialToUnion_global (b : Bool) :
    j b ≫ (U).ι = c (.initial b) := by
  cases b <;>
    simp only [arithmeticZeroInfinityNormalizedInitialToUnion, arithmeticZeroDiagonalAtlasChart,
      Category.assoc, arithmeticZeroInfinityNormalizedFullUnionIso_global,
      arithmeticZeroInfinityNormalizedPairToGlobal_first,
      arithmeticZeroInfinityNormalizedPairToGlobal_opposite,
      arithmeticZeroInfinityNormalizedToGlobal_initial]

/-- The actual initial chart in the full union has its constructed normalized comparison. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedInitialToUnion_comparison (b : Bool) :
    j b ≫ (F).hom = arithmeticZeroInfinityNormalizedPairInitial hπ data H m hj u hu b := by
  cases b <;>
    simp only [arithmeticZeroInfinityNormalizedInitialToUnion,
      arithmeticZeroInfinityNormalizedPairInitial, Bool.false_eq_true, ↓reduceIte,
      Category.assoc, arithmeticZeroInfinityNormalizedFullComparison_transport,
      arithmeticZeroInfinityNormalizedPairIso_first,
      arithmeticZeroInfinityNormalizedPairIso_opposite,
      arithmeticZeroInfinityNormalizedNodeIso_initial_assoc]

/-- The full left boundary of either entire node in the independent target pair. -/
def arithmeticZeroInfinityNormalizedTargetLeft (b : Bool) :
    branchTorus Q ⟶ arithmeticZeroInfinityNormalizedTargetPair data H m :=
  leftBranchOpen Q τ ≫ (if b then pushout.inr r r' else pushout.inl r r')

local notation "v" => arithmeticZeroInfinityNormalizedTargetLeft data H m

instance arithmeticZeroInfinityNormalizedTargetLeft_isOpenImmersion (b : Bool) :
    IsOpenImmersion (v b) := by
  unfold arithmeticZeroInfinityNormalizedTargetLeft
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- The actual retained edge keeps its complete unreduced K parameter in the full pair. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedUnion_retained (b : Bool) :
    P b ≫ j b ≫ (F).hom = (K b).hom ≫ v b := by
  rw [arithmeticZeroInfinityNormalizedInitialToUnion_comparison]
  simp only [arithmeticZeroInfinityNormalizedPairInitial,
    arithmeticZeroInfinityNormalizedTargetLeft,
    arithmeticZeroInfinityNormalizedInitial_retained_assoc]

/-- The standard target boundary has an explicit full source edge, without altering either node. -/
def arithmeticZeroInfinityNormalizedRetainedToUnion (b : Bool) :
    branchTorus Q ⟶ (U).toScheme := (K b).inv ≫ P b ≫ j b

local notation "w" => arithmeticZeroInfinityNormalizedRetainedToUnion hπ data H m hj u hu

/-- The complete reparameterized source edge has exactly the standard target boundary. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedToUnion_comparison (b : Bool) :
    w b ≫ (F).hom = v b := by
  simp only [arithmeticZeroInfinityNormalizedRetainedToUnion, Category.assoc,
    arithmeticZeroInfinityNormalizedUnion_retained, Iso.inv_hom_id_assoc]

instance arithmeticZeroInfinityNormalizedRetainedToUnion_isOpenImmersion (b : Bool) :
    IsOpenImmersion (w b) := by
  have : IsOpenImmersion (w b ≫ (F).hom) := by
    rw [arithmeticZeroInfinityNormalizedRetainedToUnion_comparison]
    infer_instance
  exact IsOpenImmersion.of_comp (w b) (F).hom

/-- The required retained node attachment keeps the full original base substitution. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedToUnion_global (b : Bool) :
    w b ≫ (U).ι = (K b).inv ≫
      (punctureSpecIso (arithmeticInitialBaseEquiv data H m 0 hj)).hom ≫
        rightBranchOpen Q ((D).last m b) ≫ c (.retained ⟨0, by omega⟩ b) := by
  simp only [arithmeticZeroInfinityNormalizedRetainedToUnion, Category.assoc,
    arithmeticZeroInfinityNormalizedInitialToUnion_global,
    arithmeticZeroDiagonalAtlas_initial_normalized]

end FLT.Mazur.WeierstrassDividedDepth

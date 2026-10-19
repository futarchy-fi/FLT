/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInfinityNormalizedRetained
public import FLT.Mazur.WeierstrassDividedOneDiagonalAtlasOverlaps

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
  arithmeticOneFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticOneFiniteAtlasIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "r" => rightBranchOpen Q τ
local notation "r'" => Iso.hom (edgeInversion Q) ≫ r
local notation "i" => arithmeticOneDiagonalOverlapToInfinity hπ data H m hj u hu
local notation "l" => arithmeticOneDiagonalInitialOverlap hπ data H m hj u hu
local notation "a" => fun b ↦ pushout.inl i (l b)
local notation "c" => arithmeticOneDiagonalAtlasChart hπ data H m hj u hu
local notation "A" => arithmeticOneFiniteAtlasObject hπ data H m m hj u hu
local notation "U" => arithmeticOneInfinityNormalizedFullUnion hπ data H m hj u hu
local notation "J" => arithmeticOneInfinityNormalizedFullUnionIso hπ data H m hj u hu
local notation "F" => arithmeticOneInfinityNormalizedFullComparison hπ data H m hj u hu
local notation "P" => arithmeticOneFiniteInitialPuncture hπ data H m m hj u hu
local notation "K" => arithmeticOneInfinityNormalizedRetainedParameter hπ data H m hj u hu
local notation "D" => arithmeticOneDiagonalState hπ data H hj u hu

/-- Each full original initial chart enters the actual three-chart open union. -/
def arithmeticOneInfinityNormalizedInitialToUnion (b : Bool) :
    A (.initial b) ⟶ (U).toScheme := by
  cases b
  · exact pushout.inr i (l false) ≫ pushout.inl (a false) (a true) ≫ (J).hom
  · exact pushout.inr i (l true) ≫ pushout.inr (a false) (a true) ≫ (J).hom

local notation "j" => arithmeticOneInfinityNormalizedInitialToUnion hπ data H m hj u hu

instance arithmeticOneInfinityNormalizedInitialToUnion_isOpenImmersion (b : Bool) :
    IsOpenImmersion (j b) := by
  cases b <;> dsimp only [arithmeticOneInfinityNormalizedInitialToUnion] <;> infer_instance

/-- The full initial source map retains its actual global inclusion. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedInitialToUnion_global (b : Bool) :
    j b ≫ (U).ι = c (.initial b) := by
  cases b <;>
    simp only [arithmeticOneInfinityNormalizedInitialToUnion, arithmeticOneDiagonalAtlasChart,
      Category.assoc, arithmeticOneInfinityNormalizedFullUnionIso_global,
      arithmeticOneInfinityNormalizedPairToGlobal_first,
      arithmeticOneInfinityNormalizedPairToGlobal_opposite,
      arithmeticOneInfinityNormalizedToGlobal_initial]

/-- The actual initial chart in the full union has its constructed normalized comparison. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedInitialToUnion_comparison (b : Bool) :
    j b ≫ (F).hom = arithmeticOneInfinityNormalizedPairInitial hπ data H m hj u hu b := by
  cases b <;>
    simp only [arithmeticOneInfinityNormalizedInitialToUnion,
      arithmeticOneInfinityNormalizedPairInitial, Bool.false_eq_true, ↓reduceIte,
      Category.assoc, arithmeticOneInfinityNormalizedFullComparison_transport,
      arithmeticOneInfinityNormalizedPairIso_first,
      arithmeticOneInfinityNormalizedPairIso_opposite,
      arithmeticOneInfinityNormalizedNodeIso_initial_assoc]

/-- The full left boundary of either entire node in the independent target pair. -/
def arithmeticOneInfinityNormalizedTargetLeft (b : Bool) :
    branchTorus Q ⟶ arithmeticOneInfinityNormalizedTargetPair data H m :=
  leftBranchOpen Q τ ≫ (if b then pushout.inr r r' else pushout.inl r r')

local notation "v" => arithmeticOneInfinityNormalizedTargetLeft data H m

instance arithmeticOneInfinityNormalizedTargetLeft_isOpenImmersion (b : Bool) :
    IsOpenImmersion (v b) := by
  unfold arithmeticOneInfinityNormalizedTargetLeft
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- The actual retained edge keeps its complete unreduced K parameter in the full pair. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedUnion_retained (b : Bool) :
    P b ≫ j b ≫ (F).hom = (K b).hom ≫ v b := by
  rw [arithmeticOneInfinityNormalizedInitialToUnion_comparison]
  simp only [arithmeticOneInfinityNormalizedPairInitial,
    arithmeticOneInfinityNormalizedTargetLeft,
    arithmeticOneInfinityNormalizedInitial_retained_assoc]

/-- The standard target boundary has an explicit full source edge, without altering either node. -/
def arithmeticOneInfinityNormalizedRetainedToUnion (b : Bool) :
    branchTorus Q ⟶ (U).toScheme := (K b).inv ≫ P b ≫ j b

local notation "w" => arithmeticOneInfinityNormalizedRetainedToUnion hπ data H m hj u hu

/-- The complete reparameterized source edge has exactly the standard target boundary. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedRetainedToUnion_comparison (b : Bool) :
    w b ≫ (F).hom = v b := by
  simp only [arithmeticOneInfinityNormalizedRetainedToUnion, Category.assoc,
    arithmeticOneInfinityNormalizedUnion_retained, Iso.inv_hom_id_assoc]

instance arithmeticOneInfinityNormalizedRetainedToUnion_isOpenImmersion (b : Bool) :
    IsOpenImmersion (w b) := by
  have : IsOpenImmersion (w b ≫ (F).hom) := by
    rw [arithmeticOneInfinityNormalizedRetainedToUnion_comparison]
    infer_instance
  exact IsOpenImmersion.of_comp (w b) (F).hom

/-- The required retained node attachment keeps the full original base substitution. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedRetainedToUnion_global (b : Bool) :
    w b ≫ (U).ι = (K b).inv ≫
      (punctureSpecIso (arithmeticInitialBaseEquiv data H m 1 hj)).hom ≫
        rightBranchOpen Q ((D).retained m 0 b) ≫ c (.retained ⟨0, by omega⟩ b) := by
  simp only [arithmeticOneInfinityNormalizedRetainedToUnion, Category.assoc,
    arithmeticOneInfinityNormalizedInitialToUnion_global,
    arithmeticOneDiagonalAtlas_initial_normalized]

end FLT.Mazur.WeierstrassDividedDepth

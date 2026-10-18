/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroExactTargetDesc
public import FLT.Mazur.WeierstrassDividedZeroCyclicSourceCharts

/-!
# Descent from the original global source through its full normalized nodes

The full source pushout comparison descends maps from the two entire initial
nodes, both original retained nodes and their one common terminal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] arithmeticZeroDiagonalAtlasChart
  finiteGlobalModel finiteGlobalContraction arithmeticZeroFiniteAtlasIso
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
  arithmeticZeroInfinityNormalizedFullComparison arithmeticZeroInfinityNormalizedGlobalComparison
  arithmeticZeroInfinityNormalizedRetainedSide
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "A" => arithmeticZeroDiagonalAtlasObject hπ data H m hj u hu
local notation "r" => rightBranchOpen Q τ
local notation "r'" => Iso.hom (edgeInversion Q) ≫ r
local notation "c" => arithmeticZeroDiagonalAtlasChart hπ data H m hj u hu
local notation "G" => arithmeticZeroInfinityNormalizedGlobalComparison hπ data H m hj u hu
local notation "U" => arithmeticZeroInfinityNormalizedFullUnion hπ data H m hj u hu
local notation "F" => arithmeticZeroInfinityNormalizedFullComparison hπ data H m hj u hu
variable {Y : Scheme}
variable (a : Bool → (PolygonSmoothing.chart (Quotient R π m) (arithmeticInitialMobiusSmoothing W
    H.a1_unit (π ^ 1) π m) ⟶ Y))
variable (ha : (rightBranchOpen (Quotient R π m) (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^
    1) π m)) ≫ a false = (Iso.hom (edgeInversion (Quotient R π m)) ≫
    (rightBranchOpen (Quotient R π m) (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m))) ≫
    a true)
variable (f : ∀ b : Bool, PolygonSmoothing.chart (Quotient R π m) (((arithmeticZeroDiagonalState hπ
    data H 0 hj u hu)).last m b) ⟶ Y)
variable (hf : ∀ b, leftBranchOpen (Quotient R π m) (arithmeticInitialMobiusSmoothing W H.a1_unit (π
    ^ 1) π m) ≫ a b =
    arithmeticZeroInfinityNormalizedRetainedSide hπ data H m hj u hu b ≫ f b)
variable (g : PolygonSmoothing.chart (Quotient R π m) (((arithmeticZeroDiagonalState hπ data H 0 hj
    u hu)).terminal m) ⟶ Y)
variable (hg : ∀ b, (edgeInversion (Quotient R π m)).hom ≫ leftBranchOpen (Quotient R π m)
    (((arithmeticZeroDiagonalState hπ data H 0 hj u hu)).last m b) ≫ f b =
    punctureOpen (((arithmeticZeroDiagonalState hπ data H 0 hj u hu)).terminal m) b ≫ g)

omit [IsBezout R] in
include hf in
/-- The whole pair map respects each original full retained attachment. -/
theorem arithmeticZeroSourcePairDesc_retained (b : Bool) :
    arithmeticZeroInfinityNormalizedTargetLeft data H m b ≫
      pushout.desc (a false) (a true) ha =
        arithmeticZeroInfinityNormalizedRetainedSide hπ data H m hj u hu b ≫ f b := by
  cases b <;>
    simpa only [arithmeticZeroInfinityNormalizedTargetLeft, Bool.false_eq_true, ↓reduceIte,
      Category.assoc, pushout.inl_desc, pushout.inr_desc] using hf _

/-- Glue compatible complete normalized nodes to a map from the actual original stage. -/
def arithmeticZeroSourceDesc : simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu ⟶ Y :=
  (G).hom ≫ arithmeticZeroExactTargetDesc hπ data H m hj u hu
    (pushout.desc (a false) (a true) ha) f
    (arithmeticZeroSourcePairDesc_retained hπ data H m hj u hu a ha f hf) g hg

local notation "d" => arithmeticZeroSourceDesc hπ data H m hj u hu a ha f hf g hg

/-- The full original initial/infinity union retains the descended pair map. -/
@[reassoc] theorem arithmeticZeroSourceDesc_union :
    (U).ι ≫ d = (F).hom ≫ pushout.desc (a false) (a true) ha := by
  rw [arithmeticZeroSourceDesc, arithmeticZeroInfinityNormalizedGlobalComparison_fullUnion_assoc,
    arithmeticZeroExactTargetDesc_pair]

/-- Both entire unreflected normalized initial nodes retain their specified maps. -/
@[reassoc] theorem arithmeticZeroSourceDesc_initial (b : Bool) :
    arithmeticZeroCyclicInitialChart hπ data H m hj u hu b ≫ d = a b := by
  simp only [arithmeticZeroCyclicInitialChart, Category.assoc,
    arithmeticZeroSourceDesc_union, Iso.inv_hom_id_assoc]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, pushout.inl_desc, pushout.inr_desc]

/-- Both original full retained nodes retain their specified maps. -/
@[reassoc] theorem arithmeticZeroSourceDesc_retained (b : Bool) :
    c (.retained ⟨0, by omega⟩ b) ≫ d = f b := by
  rw [arithmeticZeroSourceDesc, arithmeticZeroInfinityNormalizedGlobalComparison_retained_assoc,
    arithmeticZeroExactTargetDesc_retained]

/-- The entire original common terminal retains its specified map. -/
@[reassoc] theorem arithmeticZeroSourceDesc_terminal : c .terminal ≫ d = g := by
  rw [arithmeticZeroSourceDesc, arithmeticZeroInfinityNormalizedGlobalComparison_terminal_assoc,
    arithmeticZeroExactTargetDesc_terminal]

end FLT.Mazur.WeierstrassDividedDepth

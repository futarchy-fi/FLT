/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedGlobalCharts

/-!
# Descent from the complete exact-twist target

Compatible maps from the initial pair, both retained nodes and common terminal
glue through the constructed full pushouts. Both original closing edges are used.
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
  arithmeticZeroInfinityNormalizedRetainedSide arithmeticZeroInfinityNormalizedTargetLeft
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "A" => arithmeticZeroDiagonalAtlasObject hπ data H m hj u hu
local notation "r" => arithmeticZeroInfinityNormalizedRetainedSide hπ data H m hj u hu
local notation "v" => arithmeticZeroInfinityNormalizedTargetLeft data H m
local notation "t" => fun b ↦ pushout.inl (v b) (r b)
local notation "k" => arithmeticZeroInfinityNormalizedRetainedPairTargetChart hπ data H m hj u hu
local notation "b₀" => arithmeticZeroInfinityNormalizedTerminalTarget hπ data H m hj u hu
local notation "r₀" => arithmeticZeroInfinityNormalizedTerminalSide hπ data H m hj u hu
variable {Y : Scheme}
variable (p : arithmeticZeroInfinityNormalizedTargetPair data H m ⟶ Y)
variable (f : ∀ b : Bool, PolygonSmoothing.chart (Quotient R π m) (((arithmeticZeroDiagonalState hπ
    data H 0 hj u hu)).last m b) ⟶ Y)
variable (hf : ∀ b, (arithmeticZeroInfinityNormalizedTargetLeft data H m) b ≫ p =
    (arithmeticZeroInfinityNormalizedRetainedSide hπ data H m hj u hu) b ≫ f b)

/-- Attach a map from each complete original retained node to the whole normalized pair. -/
def arithmeticZeroExactAttachmentDesc (b : Bool) : pushout (v b) (r b) ⟶ Y :=
  pushout.desc p (f b) (hf b)

local notation "a" => arithmeticZeroExactAttachmentDesc hπ data H m hj u hu p f hf

/-- Both full retained attachments descend together, with the same map on their common pair. -/
def arithmeticZeroExactPairDesc :
    arithmeticZeroInfinityNormalizedRetainedPairTarget hπ data H m hj u hu ⟶ Y :=
  pushout.desc (a false) (a true) (by
    simp only [arithmeticZeroExactAttachmentDesc, pushout.inl_desc])

local notation "d" => arithmeticZeroExactPairDesc hπ data H m hj u hu p f hf

/-- The complete pair map is unchanged by descending both retained attachments. -/
@[reassoc] theorem arithmeticZeroExactPairDesc_pair :
    t false ≫ pushout.inl (t false) (t true) ≫ d = p := by
  simp only [arithmeticZeroExactPairDesc, arithmeticZeroExactAttachmentDesc,
    pushout.inl_desc]

/-- Each entire original retained node keeps its specified map after descent. -/
@[reassoc] theorem arithmeticZeroExactPairDesc_retained (b : Bool) : k b ≫ d = f b := by
  cases b <;>
    simp only [arithmeticZeroInfinityNormalizedRetainedPairTargetChart,
      arithmeticZeroExactPairDesc, arithmeticZeroExactAttachmentDesc, Category.assoc,
      pushout.inl_desc, pushout.inr_desc]

variable (g : PolygonSmoothing.chart (Quotient R π m) (((arithmeticZeroDiagonalState hπ data H 0 hj
    u hu)).terminal m) ⟶ Y)
  (hg : ∀ b, (edgeInversion (Quotient R π m)).hom ≫ leftBranchOpen (Quotient R π m)
    (((arithmeticZeroDiagonalState hπ data H 0 hj u hu)).last m b) ≫ f b =
    punctureOpen (((arithmeticZeroDiagonalState hπ data H 0 hj u hu)).terminal m) b ≫ g)

include hg in
/-- Both full closing equations hold together on the original disjoint terminal boundary. -/
theorem arithmeticZeroExactPairDesc_closing : b₀ ≫ d = r₀ ≫ g := by
  apply coprod.hom_ext <;>
    simp only [arithmeticZeroInfinityNormalizedTerminalTarget,
      arithmeticZeroInfinityNormalizedTerminalSide, coprod.inl_desc_assoc,
      coprod.inr_desc_assoc, Category.assoc, arithmeticZeroExactPairDesc_retained, hg]

variable [IsBezout R]

/-- Descend all complete charts through the actual exact-twist global target. -/
def arithmeticZeroExactTargetDesc :
    arithmeticZeroInfinityNormalizedGlobalTarget hπ data H m hj u hu ⟶ Y :=
  pushout.desc d g (arithmeticZeroExactPairDesc_closing hπ data H m hj u hu p f hf g hg)

local notation "e" => arithmeticZeroExactTargetDesc hπ data H m hj u hu p f hf g hg

/-- Descent retains the complete normalized pair. -/
@[reassoc] theorem arithmeticZeroExactTargetDesc_pair :
    arithmeticZeroInfinityNormalizedGlobalPairChart hπ data H m hj u hu ≫ e = p := by
  simp only [arithmeticZeroInfinityNormalizedGlobalPairChart,
    arithmeticZeroExactTargetDesc, Category.assoc, pushout.inl_desc,
    arithmeticZeroExactPairDesc_pair]

/-- Descent retains each full original retained node. -/
@[reassoc] theorem arithmeticZeroExactTargetDesc_retained (b : Bool) :
    arithmeticZeroInfinityNormalizedGlobalRetainedChart hπ data H m hj u hu b ≫ e = f b := by
  simp only [arithmeticZeroInfinityNormalizedGlobalRetainedChart,
    arithmeticZeroExactTargetDesc, Category.assoc, pushout.inl_desc,
    arithmeticZeroExactPairDesc_retained]

/-- Descent retains the whole common terminal. -/
@[reassoc] theorem arithmeticZeroExactTargetDesc_terminal : pushout.inr b₀ r₀ ≫ e = g :=
  pushout.inr_desc _ _ _

end FLT.Mazur.WeierstrassDividedDepth

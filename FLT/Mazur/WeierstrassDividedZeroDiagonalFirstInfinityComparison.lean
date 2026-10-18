/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalFactorRatioOverlap
public import FLT.Mazur.WeierstrassDividedZeroDiagonalFirstInfinityUnion

/-!
# Gluing the full first initial/infinity comparison on its actual source union

Both original chart maps descend to a morphism onto the entire first target
node. This is a constructed partial comparison; injectivity and extension to
the other initial and retained nodes are separate obligations.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
  arithmeticZeroFiniteAtlasIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "s" => PolygonArithmeticSimultaneous.State.initial D m false
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "l" => arithmeticZeroDiagonalInitialOverlap hπ data H m hj u hu false
local notation "i" => arithmeticZeroDiagonalOverlapToInfinity hπ data H m hj u hu
local notation "F" => arithmeticZeroDiagonalInitialFactorRatio hπ data H m hj u hu false
local notation "C" => arithmeticZeroDiagonalPolygonInitialMap hπ data H m hj u hu false
local notation "f" => arithmeticZeroDiagonalFactorRatioInitialMap hπ data H m hj u hu false
local notation "g" => arithmeticZeroDiagonalFactorRatioInfinityMap hπ data H m hj u hu
local notation "E" => arithmeticZeroDiagonalInfinityParameterIso hπ data H m hj u hu
local notation "T" => arithmeticZeroDiagonalInitialTotalNodeIso hπ data H m hj u hu false
local notation "v" => Iso.hom E ≫ rightBranchOpen Q τ ≫ Iso.hom T
local notation "U" => arithmeticZeroDiagonalFirstInfinityUnionIso hπ data H m hj u hu

/-- The full initial/infinity equation already holds inside the first complete target node. -/
@[reassoc] theorem arithmeticZeroDiagonalFirstInfinityNode_compatible : i ≫ v = l ≫ F := by
  apply (cancel_mono C).mp
  simpa only [Category.assoc, arithmeticZeroDiagonalFactorRatioInfinityMap,
    arithmeticZeroDiagonalInitialInfinityBoundary,
    arithmeticZeroDiagonalFactorRatioInitialMap] using
    arithmeticZeroDiagonalFactorRatioInfinityMap_overlap_first hπ data H m hj u hu

/-- The complete first source pair maps to its entire independently constructed target node. -/
def arithmeticZeroDiagonalFirstInfinityNodeMap :
    arithmeticZeroDiagonalFirstInfinityPushout hπ data H m hj u hu ⟶
      PolygonSmoothing.chart Q s :=
  pushout.desc v F (arithmeticZeroDiagonalFirstInfinityNode_compatible hπ data H m hj u hu)

local notation "N" => arithmeticZeroDiagonalFirstInfinityNodeMap hπ data H m hj u hu

/-- Descent keeps the full regular parameter on the whole original infinity chart. -/
@[reassoc] theorem arithmeticZeroDiagonalFirstInfinityNodeMap_infinity :
    pushout.inl i l ≫ N = v := pushout.inl_desc _ _ _

/-- Descent keeps the factor-ratio map on the whole original first initial chart. -/
@[reassoc] theorem arithmeticZeroDiagonalFirstInfinityNodeMap_initial :
    pushout.inr i l ≫ N = F := pushout.inr_desc _ _ _

/-- The infinity leg of the descended node comparison is the previously constructed target map. -/
@[reassoc] theorem arithmeticZeroDiagonalFirstInfinityNodeMap_infinity_polygon :
    pushout.inl i l ≫ N ≫ C = g := by
  rw [arithmeticZeroDiagonalFirstInfinityNodeMap_infinity_assoc]
  rfl

/-- The initial leg of the descended node comparison is the previously constructed target map. -/
@[reassoc] theorem arithmeticZeroDiagonalFirstInfinityNodeMap_initial_polygon :
    pushout.inr i l ≫ N ≫ C = f := by
  rw [arithmeticZeroDiagonalFirstInfinityNodeMap_initial_assoc]
  rfl

/-- The glued first source pair reaches every point of the whole first target node. -/
theorem arithmeticZeroDiagonalFirstInfinityNodeMap_surjective : Function.Surjective N := by
  intro x
  rcases arithmeticZeroDiagonalFactorRatioInitialInfinity_cover hπ data H m hj u hu false x
    with ⟨a, ha⟩ | ⟨a, ha⟩
  · refine ⟨pushout.inr i l a, (C).isOpenEmbedding.injective ?_⟩
    exact (congrArg (fun k ↦ k a)
      (arithmeticZeroDiagonalFirstInfinityNodeMap_initial_polygon hπ data H m hj u hu)).trans ha
  · refine ⟨pushout.inl i l a, (C).isOpenEmbedding.injective ?_⟩
    exact (congrArg (fun k ↦ k a)
      (arithmeticZeroDiagonalFirstInfinityNodeMap_infinity_polygon hπ data H m hj u hu)).trans ha

/-- The actual original source open union now has a constructed full target-node comparison. -/
def arithmeticZeroDiagonalFirstInfinityUnionNodeMap :
    (arithmeticZeroDiagonalFirstInfinityUnion hπ data H m hj u hu).toScheme ⟶
      PolygonSmoothing.chart Q s := (U).inv ≫ N

local notation "V" => arithmeticZeroDiagonalFirstInfinityUnionNodeMap hπ data H m hj u hu

/-- The union comparison recovers the full node map on its original pair presentation. -/
@[reassoc] theorem arithmeticZeroDiagonalFirstInfinityUnionNodeMap_transport :
    (U).hom ≫ V = N := by
  rw [arithmeticZeroDiagonalFirstInfinityUnionNodeMap, Iso.hom_inv_id_assoc]

/-- Every point of the first complete target node comes from the actual source open union. -/
theorem arithmeticZeroDiagonalFirstInfinityUnionNodeMap_surjective : Function.Surjective V := by
  intro x
  obtain ⟨a, ha⟩ := arithmeticZeroDiagonalFirstInfinityNodeMap_surjective hπ data H m hj u hu x
  exact ⟨(U).hom a, (congrArg (fun k ↦ k a)
    (arithmeticZeroDiagonalFirstInfinityUnionNodeMap_transport hπ data H m hj u hu)).trans ha⟩

/-- The actual source union carries a partial morphism to the independently constructed polygon. -/
def arithmeticZeroDiagonalFirstInfinityUnionComparison :
    (arithmeticZeroDiagonalFirstInfinityUnion hπ data H m hj u hu).toScheme ⟶
      arithmeticZeroDiagonalPolygon hπ data H m hj u hu := V ≫ C

/-- The image of this partial comparison is precisely the entire first target node. -/
theorem arithmeticZeroDiagonalFirstInfinityUnionComparison_range :
    Set.range (arithmeticZeroDiagonalFirstInfinityUnionComparison hπ data H m hj u hu) =
      Set.range C := by
  change Set.range (C ∘ V) = _
  rw [Set.range_comp,
    (arithmeticZeroDiagonalFirstInfinityUnionNodeMap_surjective hπ data H m hj u hu).range_eq,
    Set.image_univ]

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInfinityNormalizedNodeIso
public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedIntersection

/-!
# The exact common infinity of the two full normalized source nodes

The original initial-pair pullback shows that adjoining the same infinity
chart to both initial opens adds no further intersection between the nodes.
-/

@[expose] public noncomputable section
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
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "N" => arithmeticInitialFactorRatioChart π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "P" => arithmeticFactorRatioOverlapParameter π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "E" => arithmeticOneDiagonalInitialTotalOpenIso hπ data H m hj u hu
local notation "T" => arithmeticOneDiagonalInitialTotalNodeIso hπ data H m hj u hu
local notation "F" => arithmeticOneDiagonalInitialFactorRatio hπ data H m hj u hu
local notation "l" => arithmeticOneDiagonalInitialOverlap hπ data H m hj u hu
local notation "i" => arithmeticOneDiagonalOverlapToInfinity hπ data H m hj u hu
local notation "V" => arithmeticOneDiagonalInfinityParameterIso hπ data H m hj u hu
local notation "A" => arithmeticOneFiniteAtlasObject hπ data H m m hj u hu

local notation "f" => arithmeticOneInfinityNormalizedInitial hπ data H m hj u hu
local notation "g" => arithmeticOneInfinityNormalizedBoundary hπ data H m hj u hu
local notation "P₀" => polynomialNodeOverlapInclusion
  (W.map (algebraMap R Q)) (algebraMap R Q (π ^ 1))

local notation "c" => arithmeticOneFiniteAtlasChart hπ data H m m hj u hu
local notation "X" => simultaneousTwistedArithmeticStage hπ data H m 1 hj u hu

local notation "j" => arithmeticOneInfinityNormalizedToGlobal hπ data H m hj u hu
local notation "a" => fun b ↦ pushout.inl i (l b)

/-- The opposite initial chart meets the full first union in precisely its original D(q). -/
theorem arithmeticOneInfinityNormalizedUnion_initial_preimage :
    c (.initial true) ⁻¹' Set.range (j false) = Set.range (l true) := by
  rw [arithmeticOneInfinityNormalizedToGlobal_range, Set.preimage_union,
    fullNodePullback_preimage
      (arithmeticOneDiagonalAtlas_initial_infinity_isPullback hπ data H m hj u hu true),
    fullNodePullback_preimage
      (arithmeticOneDiagonalAtlas_initial_pair_isPullback hπ data H m hj u hu),
    Set.union_self]

/-- The two complete node unions intersect in exactly their common full infinity chart. -/
theorem arithmeticOneInfinityNormalizedNodes_preimage :
    j true ⁻¹' Set.range (j false) = Set.range (a true) := by
  ext x
  constructor
  · intro hx
    rcases SchemeOpenPushout.charts_cover i (l true) x with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact ⟨z, rfl⟩
    · have hz : c (.initial true) z ∈ Set.range (j false) := by
        change (pushout.inr i (l true) ≫ j true) z ∈ Set.range (j false) at hx
        rwa [arithmeticOneInfinityNormalizedToGlobal_initial] at hx
      have hz' : z ∈ Set.range (l true) := by
        rw [← arithmeticOneInfinityNormalizedUnion_initial_preimage hπ data H m hj u hu]
        exact hz
      obtain ⟨w, rfl⟩ := hz'
      have hc : i ≫ pushout.inl i (l true) = l true ≫ pushout.inr i (l true) :=
        pushout.condition
      exact ⟨i w, congrArg (fun k ↦ k w) hc⟩
  · rintro ⟨z, rfl⟩
    refine ⟨a false z, ?_⟩
    change (a false ≫ j false) z = (a true ≫ j true) z
    rw [arithmeticOneInfinityNormalizedToGlobal_infinity,
      arithmeticOneInfinityNormalizedToGlobal_infinity]

/-- The full source nodes have their actual common infinity as a scheme fiber product. -/
theorem arithmeticOneInfinityNormalizedNodes_isPullback :
    IsPullback (a false) (a true) (j false) (j true) := by
  apply IsOpenImmersion.isPullback _ _ _ _
  · rw [arithmeticOneInfinityNormalizedToGlobal_infinity,
      arithmeticOneInfinityNormalizedToGlobal_infinity]
  · exact TopologicalSpace.Opens.ext
      (arithmeticOneInfinityNormalizedNodes_preimage hπ data H m hj u hu)

end FLT.Mazur.WeierstrassDividedDepth

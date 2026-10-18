/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedNodeIso

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
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticZeroFiniteAtlasIso
/-- A scheme pullback has exactly the full inverse image of the opposite chart range. -/
theorem fullNodePullback_preimage {O A B X : Scheme}
    {l : O ⟶ A} {r : O ⟶ B} {f : A ⟶ X} {g : B ⟶ X}
    (H : IsPullback l r f g) : g ⁻¹' Set.range f = Set.range r := by
  ext z
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨w, _, hw⟩ := Scheme.exists_preimage_of_isPullback H a z ha
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨l w, congrArg (fun k ↦ k w) H.w⟩

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "N" => arithmeticInitialFactorRatioChart π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "P" => arithmeticFactorRatioOverlapParameter π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "E" => arithmeticZeroDiagonalInitialOpenIso hπ data H m hj u hu
local notation "T" => arithmeticZeroDiagonalInitialTotalNodeIso hπ data H m hj u hu
local notation "F" => arithmeticZeroDiagonalInitialFactorRatio hπ data H m hj u hu
local notation "l" => arithmeticZeroDiagonalInitialOverlap hπ data H m hj u hu
local notation "i" => arithmeticZeroDiagonalOverlapToInfinity hπ data H m hj u hu
local notation "V" => arithmeticZeroDiagonalInfinityParameterIso hπ data H m hj u hu
local notation "A" => arithmeticZeroFiniteAtlasObject hπ data H m m hj u hu

local notation "f" => arithmeticZeroInfinityNormalizedInitial hπ data H m hj u hu
local notation "g" => arithmeticZeroInfinityNormalizedBoundary hπ data H m hj u hu
local notation "P₀" => polynomialNodeOverlapInclusion
  (W.map (algebraMap R Q)) (algebraMap R Q (π ^ 1))

local notation "c" => arithmeticZeroFiniteAtlasChart hπ data H m m hj u hu
local notation "X" => simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu

local notation "j" => arithmeticZeroInfinityNormalizedToGlobal hπ data H m hj u hu
local notation "a" => fun b ↦ pushout.inl i (l b)

/-- The opposite initial chart meets the full first union in precisely its original D(q). -/
theorem arithmeticZeroInfinityNormalizedUnion_initial_preimage :
    c (.initial true) ⁻¹' Set.range (j false) = Set.range (l true) := by
  rw [arithmeticZeroInfinityNormalizedToGlobal_range, Set.preimage_union,
    fullNodePullback_preimage
      (arithmeticZeroDiagonalAtlas_initial_infinity_isPullback hπ data H m hj u hu true),
    fullNodePullback_preimage
      (arithmeticZeroDiagonalAtlas_initial_pair_isPullback hπ data H m hj u hu),
    Set.union_self]

/-- The two complete node unions intersect in exactly their common full infinity chart. -/
theorem arithmeticZeroInfinityNormalizedNodes_preimage :
    j true ⁻¹' Set.range (j false) = Set.range (a true) := by
  ext x
  constructor
  · intro hx
    rcases SchemeOpenPushout.charts_cover i (l true) x with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact ⟨z, rfl⟩
    · have hz : c (.initial true) z ∈ Set.range (j false) := by
        change (pushout.inr i (l true) ≫ j true) z ∈ Set.range (j false) at hx
        rwa [arithmeticZeroInfinityNormalizedToGlobal_initial] at hx
      have hz' : z ∈ Set.range (l true) := by
        rw [← arithmeticZeroInfinityNormalizedUnion_initial_preimage hπ data H m hj u hu]
        exact hz
      obtain ⟨w, rfl⟩ := hz'
      have hc : i ≫ pushout.inl i (l true) = l true ≫ pushout.inr i (l true) :=
        pushout.condition
      exact ⟨i w, congrArg (fun k ↦ k w) hc⟩
  · rintro ⟨z, rfl⟩
    refine ⟨a false z, ?_⟩
    change (a false ≫ j false) z = (a true ≫ j true) z
    rw [arithmeticZeroInfinityNormalizedToGlobal_infinity,
      arithmeticZeroInfinityNormalizedToGlobal_infinity]

/-- The full source nodes have their actual common infinity as a scheme fiber product. -/
theorem arithmeticZeroInfinityNormalizedNodes_isPullback :
    IsPullback (a false) (a true) (j false) (j true) := by
  apply IsOpenImmersion.isPullback _ _ _ _
  · rw [arithmeticZeroInfinityNormalizedToGlobal_infinity,
      arithmeticZeroInfinityNormalizedToGlobal_infinity]
  · exact TopologicalSpace.Opens.ext
      (arithmeticZeroInfinityNormalizedNodes_preimage hπ data H m hj u hu)

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentPairTransfer
public import FLT.Mazur.WeierstrassDividedArithmeticFixedSourceSmooth
public import FLT.Mazur.SchemePairBoundaryTransfer
public import FLT.Mazur.WeierstrassSuccessiveXArithmeticSmoothCover
public import FLT.Mazur.WeierstrassDividedBoundaryRangeTransport

/-!
# Smooth coverage for a single fixed indexed boundary transfer

Every nonpunctured smooth first input reaches its next horizontal puncture.
The second input remains arbitrary and unchanged.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
open scoped TensorProduct
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticRetainedTensorIso olderSuccessiveTensorAtlasIso finiteTensorAtlasObject
  PrincipalOpenTensor.transitionIso TensorProduct
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  [IsLocalRing R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (N : SplitNodeDepth W π depth)
  (hgen : IsLocalRing.maximalIdeal R = ideal R π)
  (m k : ℕ) (hk : k ≤ n) (j : ℕ) (hj : j + 2 ≤ k)
local notation "Q" => Quotient R π m
local notation "e" => data ⟨j + 1,
  Nat.lt_succ_of_le ((Nat.le_succ (j + 1)).trans (hj.trans hk))⟩
local notation "eNext" => data ⟨j + 2, by omega⟩
local notation "tt" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 0
local notation "tu" => tensorCoord W (π ^ (start + (j + 1))) π
  (Data.b3 eNext) (Data.b4 eNext) (Data.b6 eNext) Q 2
local notation "ia" => (Fin.succ ⟨k - j,
  Nat.lt_succ_of_le ((Nat.sub_le k j).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "ib" => (Fin.succ ⟨k - (j + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (j + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk

local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "f" => chart ia ≫ s
local notation "f'" => chart ib ≫ s
local notation "src" => arithmeticFixedAdjacentBoundarySource hπ data m k hk j hj
local notation "tgt" => arithmeticFixedAdjacentBoundaryTarget hπ data m k hk j hj
local notation "H" => arithmeticFixedAdjacentBoundary_ambient hπ data m k hk j hj
local notation "I" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk j hj
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj
attribute [local irreducible] arithmeticFixedAdjacentBoundarySource
  arithmeticFixedAdjacentBoundaryTarget arithmeticFixedAdjacentSourceCoordinates
  arithmeticFixedAdjacentTargetCoordinates
variable {Y : Scheme} (otherMap : Y ⟶ Spec (.of (PolygonArithmeticStages.Quotient R π m)))

local notation "O" => arithmeticFixedAdjacentPairOpen hπ data m k hk j hj otherMap
local notation "T" => arithmeticFixedAdjacentPairTransfer hπ data m k hk j hj otherMap
local notation "oldU" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2

local instance arithmeticFixedPairCoverage_structure : LocallyOfFinitePresentation s := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

include N hgen in
/-- The indexed smooth first input is covered by its puncture and actual transfer domain. -/
theorem arithmeticFixedAdjacentPairOpen_smooth_iff
    (hd : 2 * (start + j + 1) ≤ depth) (p : (pullback f otherMap : Scheme)) :
    chart ia (pullback.fst f otherMap p) ∈ (s).smoothLocus ↔
      oldU ∉ (I (pullback.fst f otherMap p)).asIdeal ∨ p ∈ O := by
  rw [arithmeticFixedAdjacentPairOpen_mem]
  exact (arithmeticFixedAdjacentSource_smooth_iff
    hπ data N hgen m k hk j hj hd (pullback.fst f otherMap p)).trans or_comm

include N hgen in
/-- Smoothness and vanishing of the horizontal coordinate force actual incidence membership. -/
theorem arithmeticFixedAdjacentPairOpen_zero_mem
    (hd : 2 * (start + j + 1) ≤ depth) (p : (pullback f otherMap : Scheme))
    (hs : chart ia (pullback.fst f otherMap p) ∈ (s).smoothLocus)
    (hz : oldU ∈ (I (pullback.fst f otherMap p)).asIdeal) : p ∈ O := by
  exact ((arithmeticFixedAdjacentPairOpen_smooth_iff
    hπ data N hgen m k hk j hj otherMap hd p).mp hs).resolve_left (not_not.mpr hz)

include N hgen in
/-- A nonpunctured smooth first input transfers without altering either original input. -/
theorem arithmeticFixedAdjacentPair_zero_target
    (hd : 2 * (start + j + 1) ≤ depth) (p : (pullback f otherMap : Scheme))
    (hs : chart ia (pullback.fst f otherMap p) ∈ (s).smoothLocus)
    (hz : oldU ∈ (I (pullback.fst f otherMap p)).asIdeal) :
    ∃ q : (pullback f' otherMap : Scheme),
      chart ib (pullback.fst f' otherMap q) = chart ia (pullback.fst f otherMap p) ∧
      pullback.snd f' otherMap q = pullback.snd f otherMap p ∧
      tu ∉ (J (pullback.fst f' otherMap q)).asIdeal := by
  let v : (O).toScheme := ⟨p, arithmeticFixedAdjacentPairOpen_zero_mem
    hπ data N hgen m k hk j hj otherMap hd p hs hz⟩
  refine ⟨T v, ?_, ?_, arithmeticFixedAdjacentPairTransfer_punctured
    hπ data m k hk j hj otherMap v⟩
  · exact congrArg (fun morphism => morphism v)
      (arithmeticFixedAdjacentPairTransfer_first hπ data m k hk j hj otherMap)
  · exact congrArg (fun morphism => morphism v)
      (arithmeticFixedAdjacentPairTransfer_second hπ data m k hk j hj otherMap)

end FLT.Mazur.WeierstrassDividedDepth

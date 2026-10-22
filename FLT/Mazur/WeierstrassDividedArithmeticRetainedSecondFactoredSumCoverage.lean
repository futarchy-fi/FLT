/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetFactoredSumCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentPairCoverage
public import FLT.Mazur.SchemePairSymmetryPoints

/-!
# Normalized sum-depth domains after transferring only the second retained input

The first punctured input keeps creation depth `i + 1`. The nonpunctured second
input moves from `j` to `j + 1`, preserving both original arithmetic inputs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticFixedAdjacentTargetCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m k : ℕ) (hk : k ≤ n) (i j : ℕ) (hi : i + 2 ≤ k) (hj : j + 2 ≤ k)
  (hij : i ≤ j) (hdepth : 2 * ((i + 1) + (j + 1)) < depth)
  (hsum : (i + 1) + (j + 1) ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨i + 2, Nat.lt_succ_of_le (hi.trans hk)⟩
local notation "ej" => data ⟨j + 2, Nat.lt_succ_of_le (hj.trans hk)⟩
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - (j + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (j + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj

local notation "di" => data ⟨i + 1, by omega⟩
local notation "dj" => data ⟨j + 1,
  Nat.lt_succ_of_le ((Nat.le_succ (j + 1)).trans (hj.trans hk))⟩
local notation "U" => (finiteGlobalStructure hπ data k hk).smoothLocus

local notation "O₊" => arithmeticTargetFactoredSumPositiveOpen node data m k hk i j hi hj
  hij (by omega) hsum
local notation "O₋" => arithmeticTargetFactoredSumNegativeOpen node data m k hk i j hi hj
  hij (by omega) hsum
local notation "O₀" => arithmeticTargetFactoredSumOppositeOpen node data m k hk i j hi hj hij hsum
local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "v" => tensorCoord W (π ^ (0 + (j + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2

local notation "oldIndex" => (Fin.succ ⟨k - j,
  Nat.lt_succ_of_le ((Nat.sub_le k j).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "oldCoords" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk j hj
local notation "oldU" => tensorCoord W (π ^ (0 + j)) π
  (Data.b3 dj) (Data.b4 dj) (Data.b6 dj) Q 2
local notation "f" => chart c ≫ s
local notation "g" => chart oldIndex ≫ s
local notation "g'" => chart d ≫ s
local notation "swap" => (pullbackSymmetry f g).hom
local notation "back" => (pullbackSymmetry g' f).hom

local instance arithmeticSecondFactoredSumCoverage_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

include hdepth in
/-- A punctured/nonpunctured mixed pair reaches an actual domain with its input order intact. -/
theorem arithmeticRetainedSecond_zero_factoredSum_target
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hlt : i < j)
    (p : (pullback f g : Scheme))
    (hs : chart oldIndex (pullback.snd f g p) ∈ (s).smoothLocus)
    (hx : u ∉ (I (pullback.fst f g p)).asIdeal)
    (hy : oldU ∈ (oldCoords (pullback.snd f g p)).asIdeal) :
    ∃ q : (pullback f g' : Scheme),
      pullback.fst f g' q = pullback.fst f g p ∧
      chart d (pullback.snd f g' q) = chart oldIndex (pullback.snd f g p) ∧
      (q ∈ O₊ ∨ q ∈ O₋ ∨ q ∈ O₀) := by
  have hs' : chart oldIndex (pullback.fst g f (swap p)) ∈ (s).smoothLocus := by
    rw [SchemePairSymmetryPoints.fst_apply]
    exact hs
  have hy' : oldU ∈ (oldCoords (pullback.fst g f (swap p))).asIdeal := by
    rw [SchemePairSymmetryPoints.fst_apply]
    exact hy
  obtain ⟨q, hq, he, hv⟩ := arithmeticFixedAdjacentPair_zero_target
    hπ data node hgen m k hk j hj f (by omega) (swap p) hs' hy'
  rw [SchemePairSymmetryPoints.fst_apply] at hq
  rw [SchemePairSymmetryPoints.snd_apply] at he
  refine ⟨back q, ?_, ?_, ?_⟩
  · rw [SchemePairSymmetryPoints.fst_apply]
    exact he
  · rw [SchemePairSymmetryPoints.snd_apply]
    exact hq
  · apply arithmeticTargetFactoredSum_punctured_cover node data m k hk i j hi hj
      hij (by omega) hsum hdepth
      hlt (back q)
    · rw [SchemePairSymmetryPoints.fst_apply, he]
      exact hx
    · rw [SchemePairSymmetryPoints.snd_apply]
      exact hv

end FLT.Mazur.WeierstrassDividedDepth

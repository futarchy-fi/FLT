/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedDoubleIncidence
public import FLT.Mazur.WeierstrassDividedArithmeticFixedSourceSmooth
public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentRange

/-!
# Full smooth source coverage for two independent retained depths

The original coordinate tests partition smooth pairs into the punctured,
mixed one-transfer, and simultaneous-transfer regions. Each input retains
its own explicit numeric depth bound, including when its creation depth is zero.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  arithmeticFixedAdjacentBoundarySource arithmeticFixedAdjacentBoundaryTarget
  arithmeticFixedAdjacentSourceCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (N : SplitNodeDepth W π depth)
  (hgen : IsLocalRing.maximalIdeal R = PolygonArithmeticStages.ideal R π)
  (m k : ℕ) (hk : k ≤ n) (i j : ℕ) (hi : i + 2 ≤ k) (hj : j + 2 ≤ k)
local notation "a" => (Fin.succ ⟨k - i,
  Nat.lt_succ_of_le ((Nat.sub_le k i).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "b" => (Fin.succ ⟨k - j,
  Nat.lt_succ_of_le ((Nat.sub_le k j).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - (j + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (j + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "x" => arithmeticFixedAdjacentBoundarySource hπ data m k hk i hi
local notation "z" => arithmeticFixedAdjacentBoundaryTarget hπ data m k hk i hi
local notation "y" => arithmeticFixedAdjacentBoundarySource hπ data m k hk j hj
local notation "w" => arithmeticFixedAdjacentBoundaryTarget hπ data m k hk j hj
local notation "hx" => arithmeticFixedAdjacentBoundary_ambient hπ data m k hk i hi
local notation "hy" => arithmeticFixedAdjacentBoundary_ambient hπ data m k hk j hj

local notation "D" => arithmeticRetainedDoubleOpen hπ data m k hk i j hi hj
local notation "t" => arithmeticRetainedDoubleTransfer hπ data m k hk i j hi hj

local notation "Q" => PolygonArithmeticStages.Quotient R π m
local notation "ei" => data ⟨i + 1, by omega⟩
local notation "ej" => data ⟨j + 1, by omega⟩
local notation "ti" => WeierstrassSuccessiveX.tensorCoord W (π ^ (start + i)) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 0
local notation "tj" => WeierstrassSuccessiveX.tensorCoord W (π ^ (start + j)) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 0
local notation "I" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk i hi
local notation "J" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk j hj
local notation "f" => chart a ≫ s
local notation "g" => chart b ≫ s
local notation "f'" => chart c ≫ s
local notation "g'" => chart d ≫ s

local notation "ui" => WeierstrassSuccessiveX.tensorCoord W (π ^ (start + i)) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "uj" => WeierstrassSuccessiveX.tensorCoord W (π ^ (start + j)) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2

local instance arithmeticDoubleCoverage_structure : LocallyOfFinitePresentation s := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

include N hgen in
/-- Two smooth nonpunctured inputs of independent depths lie in the actual double domain. -/
theorem arithmeticRetainedDoubleOpen_anyDepth_zero_mem
    (hdi : 2 * (start + i + 1) ≤ depth) (hdj : 2 * (start + j + 1) ≤ depth)
    (p : (pullback f g : Scheme))
    (hsi : chart a (pullback.fst f g p) ∈ (s).smoothLocus)
    (hsj : chart b (pullback.snd f g p) ∈ (s).smoothLocus)
    (hui : ui ∈ (I (pullback.fst f g p)).asIdeal)
    (huj : uj ∈ (J (pullback.snd f g p)).asIdeal) : p ∈ D := by
  have hi' := (arithmeticFixedAdjacentSource_smooth_iff hπ data N hgen m k hk i hi
    hdi (pullback.fst f g p)).mp hsi
  have hj' := (arithmeticFixedAdjacentSource_smooth_iff hπ data N hgen m k hk j hj
    hdj (pullback.snd f g p)).mp hsj
  exact (arithmeticRetainedDoubleOpen_mem_incidence hπ data m k hk i j hi hj p).mpr
    ⟨hi'.resolve_right (not_not.mpr hui), hj'.resolve_right (not_not.mpr huj)⟩

include N hgen in
/-- The four incidence/puncture regions cover every smooth independent-depth source pair. -/
theorem arithmeticRetainedDouble_anyDepth_four_regions
    (hdi : 2 * (start + i + 1) ≤ depth) (hdj : 2 * (start + j + 1) ≤ depth)
    (p : (pullback f g : Scheme))
    (hsi : chart a (pullback.fst f g p) ∈ (s).smoothLocus)
    (hsj : chart b (pullback.snd f g p) ∈ (s).smoothLocus) :
    (ui ∉ (I (pullback.fst f g p)).asIdeal ∧ uj ∉ (J (pullback.snd f g p)).asIdeal) ∨
    (ui ∉ (I (pullback.fst f g p)).asIdeal ∧ tj ∉ (J (pullback.snd f g p)).asIdeal) ∨
    (ti ∉ (I (pullback.fst f g p)).asIdeal ∧ uj ∉ (J (pullback.snd f g p)).asIdeal) ∨
    p ∈ D := by
  have hi' := (arithmeticFixedAdjacentSource_smooth_iff hπ data N hgen m k hk i hi
    hdi (pullback.fst f g p)).mp hsi
  have hj' := (arithmeticFixedAdjacentSource_smooth_iff hπ data N hgen m k hk j hj
    hdj (pullback.snd f g p)).mp hsj
  rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj'
  · exact Or.inr (Or.inr (Or.inr
      ((arithmeticRetainedDoubleOpen_mem_incidence hπ data m k hk i j hi hj p).mpr ⟨hi', hj'⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨hi', hj'⟩))
  · exact Or.inr (Or.inl ⟨hi', hj'⟩)
  · exact Or.inl ⟨hi', hj'⟩

local notation "eiNext" => data ⟨i + 2, by omega⟩
local notation "ejNext" => data ⟨j + 2, by omega⟩
local notation "vi" => WeierstrassSuccessiveX.tensorCoord W (π ^ (start + (i + 1))) π
  (Data.b3 eiNext) (Data.b4 eiNext) (Data.b6 eiNext) Q 2
local notation "vj" => WeierstrassSuccessiveX.tensorCoord W (π ^ (start + (j + 1))) π
  (Data.b3 ejNext) (Data.b4 ejNext) (Data.b6 ejNext) Q 2
local notation "I'" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "J'" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj

include N hgen in
/-- Both nonpunctured smooth inputs acquire actual punctured target coordinates simultaneously. -/
theorem arithmeticRetainedDouble_anyDepth_zero_coordinates
    (hdi : 2 * (start + i + 1) ≤ depth) (hdj : 2 * (start + j + 1) ≤ depth)
    (p : (pullback f g : Scheme))
    (hsi : chart a (pullback.fst f g p) ∈ (s).smoothLocus)
    (hsj : chart b (pullback.snd f g p) ∈ (s).smoothLocus)
    (hui : ui ∈ (I (pullback.fst f g p)).asIdeal)
    (huj : uj ∈ (J (pullback.snd f g p)).asIdeal) :
    ∃ q : (pullback f' g' : Scheme),
      chart c (pullback.fst f' g' q) = chart a (pullback.fst f g p) ∧
      chart d (pullback.snd f' g' q) = chart b (pullback.snd f g p) ∧
      vi ∉ (I' (pullback.fst f' g' q)).asIdeal ∧
      vj ∉ (J' (pullback.snd f' g' q)).asIdeal := by
  let v : (D).toScheme := ⟨p, arithmeticRetainedDoubleOpen_anyDepth_zero_mem
    hπ data N hgen m k hk i j hi hj hdi hdj p hsi hsj hui huj⟩
  refine ⟨t v, ?_, ?_, arithmeticRetainedDoubleTransfer_punctured hπ data m k hk i j hi hj v⟩
  · exact congrArg (fun morphism => morphism v)
      (arithmeticRetainedDoubleTransfer_first hπ data m k hk i j hi hj)
  · exact congrArg (fun morphism => morphism v)
      (arithmeticRetainedDoubleTransfer_second hπ data m k hk i j hi hj)

end FLT.Mazur.WeierstrassDividedDepth

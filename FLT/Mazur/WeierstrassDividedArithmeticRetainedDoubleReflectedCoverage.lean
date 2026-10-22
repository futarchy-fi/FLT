/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetReflectedCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedDoubleCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticFixedSourceSmooth
public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentRange

/-!
# Reflected-domain coverage of nonpunctured retained pairs

The actual simultaneous transfer reaches one of the three constructed output
domains. Both original arithmetic inputs are preserved. The target depth bounds
are explicit and supply the source smoothness bounds.
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
  {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (N : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (hgen : IsLocalRing.maximalIdeal R = PolygonArithmeticStages.ideal R π)
  (m k : ℕ) (hk : k ≤ n) (i j : ℕ) (hi : i + 2 ≤ k) (hj : j + 2 ≤ k)
local notation "hπ" => N.uniformizer_ne_zero
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
local notation "ti" => WeierstrassSuccessiveX.tensorCoord W (π ^ (0 + i)) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 0
local notation "tj" => WeierstrassSuccessiveX.tensorCoord W (π ^ (0 + j)) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 0
local notation "I" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk i hi
local notation "J" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk j hj
local notation "f" => chart a ≫ s
local notation "g" => chart b ≫ s
local notation "f'" => chart c ≫ s
local notation "g'" => chart d ≫ s

local notation "ui" => WeierstrassSuccessiveX.tensorCoord W (π ^ (0 + i)) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "uj" => WeierstrassSuccessiveX.tensorCoord W (π ^ (0 + j)) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2

local instance arithmeticDoubleReflectedCoverage_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

variable (hij : i ≤ j) (hlo : 2 * (j + 1) < depth)
  (hhi : depth ≤ (i + 1) + 2 * (j + 1))
  (hstage : depth - (i + 1) - (j + 1) ≤ k)
local notation "O₊" => arithmeticTargetReflectedPositiveOpen N data m k hk i j hi hj
  hij hlo hhi hstage
local notation "O₋" => arithmeticTargetReflectedNegativeOpen N data m k hk i j hi hj
  hij hlo hhi hstage
local notation "O₀" =>
  arithmeticTargetReflectedOppositeOpen N data m k hk i j hi hj hij hlo hhi hstage

include hgen in
/-- Nonpunctured smooth inputs reach an actual addition domain with both inputs unchanged. -/
theorem arithmeticRetainedDouble_zero_reflected_target (hlt : i < j)
    (p : (pullback f g : Scheme))
    (hsi : chart a (pullback.fst f g p) ∈ (s).smoothLocus)
    (hsj : chart b (pullback.snd f g p) ∈ (s).smoothLocus)
    (hui : ui ∈ (I (pullback.fst f g p)).asIdeal)
    (huj : uj ∈ (J (pullback.snd f g p)).asIdeal) :
    ∃ q : (pullback f' g' : Scheme),
      chart c (pullback.fst f' g' q) = chart a (pullback.fst f g p) ∧
      chart d (pullback.snd f' g' q) = chart b (pullback.snd f g p) ∧
      (q ∈ O₊ ∨ q ∈ O₋ ∨ q ∈ O₀) := by
  let v : (D).toScheme := ⟨p, arithmeticRetainedDoubleOpen_anyDepth_zero_mem
    hπ data N hgen m k hk i j hi hj (by omega) (by omega) p hsi hsj hui huj⟩
  refine ⟨t v, ?_, ?_, arithmeticRetainedDoubleTransfer_reflected_cover
    N data m k hk i j hi hj hij hlo hhi hstage hlt v⟩
  · exact congrArg (fun morphism => morphism v)
      (arithmeticRetainedDoubleTransfer_first hπ data m k hk i j hi hj)
  · exact congrArg (fun morphism => morphism v)
      (arithmeticRetainedDoubleTransfer_second hπ data m k hk i j hi hj)

end FLT.Mazur.WeierstrassDividedDepth

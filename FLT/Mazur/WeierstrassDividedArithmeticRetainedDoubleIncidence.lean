/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedDoublePuncture
public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentRange

/-!
# Exact incidence tests for simultaneous arithmetic boundary transfer

Both independent retained depths use their original incidence coordinates.
These tests give an actual target pair with punctured coordinates and unchanged
ambient inputs, including when one or both creation depths are zero.
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
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
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

/-- The complete simultaneous domain is exactly both original incidence tests. -/
theorem arithmeticRetainedDoubleOpen_mem_incidence (p : (pullback f g : Scheme)) :
    p ∈ D ↔ ti ∉ (I (pullback.fst f g p)).asIdeal ∧
      tj ∉ (J (pullback.snd f g p)).asIdeal := by
  change (pullback.fst f g p ∈ Set.range x ∧ pullback.snd f g p ∈ Set.range y) ↔ _
  exact and_congr
    (arithmeticFixedAdjacentBoundarySource_mem hπ data m k hk i hi _)
    (arithmeticFixedAdjacentBoundarySource_mem hπ data m k hk j hj _)

/-- Original incidence conditions construct the whole transferred pair without losing inputs. -/
theorem arithmeticRetainedDouble_incidence_target (p : (pullback f g : Scheme))
    (hi' : ti ∉ (I (pullback.fst f g p)).asIdeal)
    (hj' : tj ∉ (J (pullback.snd f g p)).asIdeal) :
    ∃ q : (pullback f' g' : Scheme),
      chart c (pullback.fst f' g' q) = chart a (pullback.fst f g p) ∧
      chart d (pullback.snd f' g' q) = chart b (pullback.snd f g p) ∧
      pullback.fst f' g' q ∈ Set.range z ∧ pullback.snd f' g' q ∈ Set.range w := by
  let v : (D).toScheme :=
    ⟨p, (arithmeticRetainedDoubleOpen_mem_incidence hπ data m k hk i j hi hj p).mpr
      ⟨hi', hj'⟩⟩
  refine ⟨t v, ?_, ?_, arithmeticRetainedDoubleTransfer_ranges hπ data m k hk i j hi hj v⟩
  · exact congrArg (fun morphism => morphism v)
      (arithmeticRetainedDoubleTransfer_first hπ data m k hk i j hi hj)
  · exact congrArg (fun morphism => morphism v)
      (arithmeticRetainedDoubleTransfer_second hπ data m k hk i j hi hj)

end FLT.Mazur.WeierstrassDividedDepth

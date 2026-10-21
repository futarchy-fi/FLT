/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedDouble
public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentPuncture
public import FLT.Mazur.SchemePairDoubleBoundaryRange

/-!
# Both arbitrary retained transfers land in the full horizontal punctures

The actual composed boundary map supplies both nonvanishing conditions.
They are consequences of the original incidence domain, not new premises.
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

/-- Both transferred inputs lie in their actual target boundary ranges. -/
theorem arithmeticRetainedDoubleTransfer_ranges (p : (D).toScheme) :
    pullback.fst (chart c ≫ s) (chart d ≫ s) (t p) ∈ Set.range z ∧
      pullback.snd (chart c ≫ s) (chart d ≫ s) (t p) ∈ Set.range w := by
  constructor
  · exact SchemePairDoubleBoundary.transfer_fst_mem_range
      (chart a ≫ s) (chart c ≫ s) (chart b ≫ s) (chart d ≫ s) x z y w _ _ p
  · exact SchemePairDoubleBoundary.transfer_snd_mem_range
      (chart a ≫ s) (chart c ≫ s) (chart b ≫ s) (chart d ≫ s) x z y w _ _ p

local notation "Q" => PolygonArithmeticStages.Quotient R π m
local notation "ei" => data ⟨i + 2, by omega⟩
local notation "ej" => data ⟨j + 2, by omega⟩
local notation "u" => WeierstrassSuccessiveX.tensorCoord W (π ^ (start + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "v" => WeierstrassSuccessiveX.tensorCoord W (π ^ (start + (j + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2
local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj

/-- Both uncontracted next-chart horizontal coordinates are nonzero on the whole domain. -/
theorem arithmeticRetainedDoubleTransfer_punctured (p : (D).toScheme) :
    u ∉ (I (pullback.fst (chart c ≫ s) (chart d ≫ s) (t p))).asIdeal ∧
      v ∉ (J (pullback.snd (chart c ≫ s) (chart d ≫ s) (t p))).asIdeal := by
  have hp := arithmeticRetainedDoubleTransfer_ranges hπ data m k hk i j hi hj p
  exact ⟨arithmeticFixedAdjacentBoundaryTarget_punctured hπ data m k hk i hi _ hp.1,
    arithmeticFixedAdjacentBoundaryTarget_punctured hπ data m k hk j hj _ hp.2⟩

end FLT.Mazur.WeierstrassDividedDepth

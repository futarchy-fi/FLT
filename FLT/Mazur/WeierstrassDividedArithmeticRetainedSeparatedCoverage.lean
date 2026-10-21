/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedDoubleAdditionCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedSingleAdditionCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedSecondAdditionCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentCoordinateShift

/-!
# Complete smooth coverage for separated positive retained depths

Each input either keeps its creation depth or advances once. The four cases
all reach an actual constructed addition domain, with both ambient inputs
unchanged. The separation and target depth bounds remain explicit.
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
  (hiNext : (i + 1) + 2 ≤ k) (hjNext : (j + 1) + 2 ≤ k)
  (hgap : i + 1 < j) (hdepth : 4 * (j + 2) ≤ depth)
  (hsum : (i + 2) + (j + 2) ≤ k) (h2 : W.a₂ = 0)
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
local notation "dj" => data ⟨j + 1, by omega⟩
local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "v" => tensorCoord W (π ^ (0 + (j + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2

local notation "index" => fun r : ℕ => (Fin.succ ⟨k - r,
  Nat.lt_succ_of_le ((Nat.sub_le k r).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "f" => chart c ≫ s
local notation "g" => chart d ≫ s

local instance arithmeticSeparatedCoverage_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

include hi hj hiNext hjNext hgap hdepth hsum in
/-- Every smooth pair in this range reaches an actual addition domain after at most one shift. -/
theorem arithmeticRetainedSeparated_smooth_addition_target
    (hgen : IsLocalRing.maximalIdeal R = ideal R π)
    (p : (pullback f g : Scheme))
    (hsi : chart c (pullback.fst f g p) ∈ (s).smoothLocus)
    (hsj : chart d (pullback.snd f g p) ∈ (s).smoothLocus) :
    ∃ (r t : ℕ) (hr : r + 2 ≤ k) (ht : t + 2 ≤ k) (hrt : r ≤ t)
      (hd : 4 * (t + 1) ≤ depth) (hs : (r + 1) + (t + 1) ≤ k)
      (q : (pullback (chart (index (r + 1)) ≫ s) (chart (index (t + 1)) ≫ s) : Scheme)),
      (r = i ∨ r = i + 1) ∧ (t = j ∨ t = j + 1) ∧
      chart (index (r + 1))
        (pullback.fst (chart (index (r + 1)) ≫ s) (chart (index (t + 1)) ≫ s) q) =
          chart c (pullback.fst f g p) ∧
      chart (index (t + 1))
        (pullback.snd (chart (index (r + 1)) ≫ s) (chart (index (t + 1)) ≫ s) q) =
          chart d (pullback.snd f g p) ∧
      (q ∈ arithmeticTargetPairPositiveOpen node data m k hk r t hr ht hrt hd hs h2 ∨
        q ∈ arithmeticTargetPairNegativeOpen node data m k hk r t hr ht hrt hd hs h2 ∨
        q ∈ arithmeticTargetPairOppositeOpen node data m k hk r t hr ht hrt hs) := by
  classical
  by_cases hx : u ∈ (I (pullback.fst f g p)).asIdeal
  · have hx' := hx
    rw [arithmeticFixedAdjacentTargetCoordinates_eq_next_source
      hπ data m k hk i hi hiNext] at hx'
    by_cases hy : v ∈ (J (pullback.snd f g p)).asIdeal
    · have hy' := hy
      rw [arithmeticFixedAdjacentTargetCoordinates_eq_next_source
        hπ data m k hk j hj hjNext] at hy'
      obtain ⟨q, hq₁, hq₂, hq⟩ := arithmeticRetainedDouble_zero_addition_target
        node data hgen m k hk (i + 1) (j + 1) hiNext hjNext (by omega)
        (by omega) (by omega) h2 (by omega) p hsi hsj hx' hy'
      exact ⟨i + 1, j + 1, hiNext, hjNext, by omega, by omega, by omega,
        q, Or.inr rfl, Or.inr rfl, hq₁, hq₂, hq⟩
    · obtain ⟨q, hq₁, hq₂, hq⟩ := arithmeticRetainedSingle_zero_addition_target
        node data m k hk (i + 1) j hiNext hj (by omega) (by omega) (by omega) h2
        hgen hgap p hsi hx' hy
      exact ⟨i + 1, j, hiNext, hj, by omega, by omega, by omega,
        q, Or.inr rfl, Or.inl rfl, hq₁, congrArg (chart d) hq₂, hq⟩
  · by_cases hy : v ∈ (J (pullback.snd f g p)).asIdeal
    · have hy' := hy
      rw [arithmeticFixedAdjacentTargetCoordinates_eq_next_source
        hπ data m k hk j hj hjNext] at hy'
      obtain ⟨q, hq₁, hq₂, hq⟩ := arithmeticRetainedSecond_zero_addition_target
        node data m k hk i (j + 1) hi hjNext (by omega) (by omega) (by omega) h2
        hgen (by omega) p hsj hx hy'
      exact ⟨i, j + 1, hi, hjNext, by omega, by omega, by omega,
        q, Or.inl rfl, Or.inr rfl, congrArg (chart c) hq₁, hq₂, hq⟩
    · exact ⟨i, j, hi, hj, by omega, by omega, by omega, p,
        Or.inl rfl, Or.inl rfl, rfl, rfl,
        arithmeticTargetPair_punctured_cover node data m k hk i j hi hj
          (by omega) (by omega) (by omega) h2 (by omega) p hx hy⟩

end FLT.Mazur.WeierstrassDividedDepth

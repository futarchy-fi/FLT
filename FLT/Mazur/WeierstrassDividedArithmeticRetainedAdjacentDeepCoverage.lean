/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetSelfDeepAddition
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedSecondAdditionCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedDoubleAdditionCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentCoordinateShift

/-!
# Complete adjacent retained coverage in the deep range

Only the first-shift case has equal target depths. Its actual deep and
reciprocal outputs complete the three previously unequal-depth cases.
Both original arithmetic input points are preserved in their original order.
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
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i + 2 ≤ k) (hiNext : (i + 1) + 2 ≤ k)
  (hiNextNext : (i + 2) + 2 ≤ k)
  (hdepth : 4 * (i + 3) < depth) (hsum : (i + 3) + (i + 3) ≤ k) (h2 : W.a₂ = 0)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "e" => data ⟨i + 2, Nat.lt_succ_of_le (hi.trans hk)⟩
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - ((i + 1) + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k ((i + 1) + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "f" => chart c ≫ s
local notation "g" => chart d ≫ s
local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2
local notation "en" => data ⟨(i + 1) + 2, Nat.lt_succ_of_le (hiNext.trans hk)⟩
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk (i + 1) hiNext
local notation "v" => tensorCoord W (π ^ (0 + ((i + 1) + 1))) π
  (Data.b3 en) (Data.b4 en) (Data.b6 en) Q 2
local notation "D" => arithmeticTargetSelfDeepOpen node data m k hk (i + 1) hiNext
  (by omega)
local notation "C" => arithmeticTargetSelfReciprocalOpen node data m k hk (i + 1) hiNext
local notation "index" => fun r : ℕ => (Fin.succ ⟨k - r,
  Nat.lt_succ_of_le ((Nat.sub_le k r).trans (Nat.le_succ k))⟩ : Fin (k + 3))

local instance arithmeticAdjacentDeepCoverage_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

include hi hiNextNext hdepth hsum in
/-- Every adjacent smooth pair reaches a constructed output, including equal shifted targets. -/
theorem arithmeticRetainedAdjacentDeep_smooth_addition_target
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (p : (pullback f g : Scheme))
    (hsi : chart c (pullback.fst f g p) ∈ (s).smoothLocus)
    (hsj : chart d (pullback.snd f g p) ∈ (s).smoothLocus) :
    (∃ (r t : ℕ) (hr : r + 2 ≤ k) (ht : t + 2 ≤ k) (hrt : r ≤ t)
      (hd : 4 * (t + 1) ≤ depth) (hs : (r + 1) + (t + 1) ≤ k)
      (q : (pullback (chart (index (r + 1)) ≫ s) (chart (index (t + 1)) ≫ s) : Scheme)),
      (r = i ∨ r = i + 1) ∧ (t = i + 1 ∨ t = i + 2) ∧
      chart (index (r + 1))
        (pullback.fst (chart (index (r + 1)) ≫ s) (chart (index (t + 1)) ≫ s) q) =
          chart c (pullback.fst f g p) ∧
      chart (index (t + 1))
        (pullback.snd (chart (index (r + 1)) ≫ s) (chart (index (t + 1)) ≫ s) q) =
          chart d (pullback.snd f g p) ∧
      (q ∈ arithmeticTargetPairPositiveOpen node data m k hk r t hr ht hrt hd hs h2 ∨
        q ∈ arithmeticTargetPairNegativeOpen node data m k hk r t hr ht hrt hd hs h2 ∨
        q ∈ arithmeticTargetPairOppositeOpen node data m k hk r t hr ht hrt hs)) ∨
    (∃ q : (pullback g g : Scheme),
      chart d (pullback.fst g g q) = chart c (pullback.fst f g p) ∧
      pullback.snd g g q = pullback.snd f g p ∧ (q ∈ D ∨ q ∈ C)) := by
  classical
  by_cases hx : u ∈ (I (pullback.fst f g p)).asIdeal
  · have hx' := hx
    rw [arithmeticFixedAdjacentTargetCoordinates_eq_next_source
      hπ data m k hk i hi hiNext] at hx'
    by_cases hy : v ∈ (J (pullback.snd f g p)).asIdeal
    · have hy' := hy
      rw [arithmeticFixedAdjacentTargetCoordinates_eq_next_source
        hπ data m k hk (i + 1) hiNext hiNextNext] at hy'
      obtain ⟨q, hq₁, hq₂, hq⟩ := arithmeticRetainedDouble_zero_addition_target
        node data hgen m k hk (i + 1) (i + 2) hiNext hiNextNext (by omega)
        (by omega) (by omega) h2 (by omega) p hsi hsj hx' hy'
      exact Or.inl ⟨i + 1, i + 2, hiNext, hiNextNext, by omega, by omega, by omega,
        q, Or.inr rfl, Or.inr rfl, hq₁, hq₂, hq⟩
    · obtain ⟨q, hq, he, hv⟩ := arithmeticFixedAdjacentPair_zero_target
        hπ data node hgen m k hk (i + 1) hiNext g (by omega) p hsi hx'
      refine Or.inr ⟨q, hq, he, ?_⟩
      apply arithmeticTargetSelfDeep_punctured_cover node data m k hk (i + 1) hiNext
        (by omega) (by omega) q hv
      rw [he]
      exact hy
  · by_cases hy : v ∈ (J (pullback.snd f g p)).asIdeal
    · have hy' := hy
      rw [arithmeticFixedAdjacentTargetCoordinates_eq_next_source
        hπ data m k hk (i + 1) hiNext hiNextNext] at hy'
      obtain ⟨q, hq₁, hq₂, hq⟩ := arithmeticRetainedSecond_zero_addition_target
        node data m k hk i (i + 2) hi hiNextNext (by omega) (by omega) (by omega) h2
        hgen (by omega) p hsj hx hy'
      exact Or.inl ⟨i, i + 2, hi, hiNextNext, by omega, by omega, by omega,
        q, Or.inl rfl, Or.inr rfl, congrArg (chart c) hq₁, hq₂, hq⟩
    · exact Or.inl ⟨i, i + 1, hi, hiNext, by omega, by omega, by omega, p,
        Or.inl rfl, Or.inl rfl, rfl, rfl,
        arithmeticTargetPair_punctured_cover node data m k hk i (i + 1) hi hiNext
          (by omega) (by omega) (by omega) h2 (by omega) p hx hy⟩

end FLT.Mazur.WeierstrassDividedDepth

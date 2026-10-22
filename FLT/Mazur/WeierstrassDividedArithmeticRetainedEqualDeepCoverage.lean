/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetSelfDeepAddition
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedSecondAdditionCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedDoubleCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentCoordinateShift

/-!
# Full equal-retained-depth coverage in the deep range

Each input either keeps its creation depth or advances once. All four cases
reach actual constructed addition domains. In the reversed mixed case the
ordered target explicitly records the permutation of the two original inputs.
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
  (hdepth : 4 * (i + 2) < depth) (hsum : (i + 2) + (i + 2) ≤ k) (h2 : W.a₂ = 0)
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
local notation "D" => arithmeticTargetSelfDeepOpen node data m k hk i hi (by omega)
local notation "C" => arithmeticTargetSelfReciprocalOpen node data m k hk i hi
local notation "D'" => arithmeticTargetSelfDeepOpen node data m k hk (i + 1) hiNext
  (by omega)
local notation "C'" => arithmeticTargetSelfReciprocalOpen node data m k hk (i + 1) hiNext
local notation "O₊" => arithmeticTargetPairPositiveOpen node data m k hk i (i + 1)
  hi hiNext (by omega) (by omega) (by omega) h2
local notation "O₋" => arithmeticTargetPairNegativeOpen node data m k hk i (i + 1)
  hi hiNext (by omega) (by omega) (by omega) h2
local notation "O₀" => arithmeticTargetPairOppositeOpen node data m k hk i (i + 1)
  hi hiNext (by omega) (by omega)

local instance arithmeticEqualDeepCoverage_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Every smooth positive equal-depth pair reaches an actual deep or mixed output domain. -/
theorem arithmeticRetainedEqualDeep_smooth_addition_target
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (p : (pullback f f : Scheme))
    (hs : chart c (pullback.fst f f p) ∈ (s).smoothLocus)
    (ht : chart c (pullback.snd f f p) ∈ (s).smoothLocus) :
    (p ∈ D ∨ p ∈ C) ∨
    (∃ q : (pullback f g : Scheme),
      pullback.fst f g q = pullback.fst f f p ∧
      chart d (pullback.snd f g q) = chart c (pullback.snd f f p) ∧
      (q ∈ O₊ ∨ q ∈ O₋ ∨ q ∈ O₀)) ∨
    (∃ q : (pullback f g : Scheme),
      pullback.fst f g q = pullback.snd f f p ∧
      chart d (pullback.snd f g q) = chart c (pullback.fst f f p) ∧
      (q ∈ O₊ ∨ q ∈ O₋ ∨ q ∈ O₀)) ∨
    (∃ q : (pullback g g : Scheme),
      chart d (pullback.fst g g q) = chart c (pullback.fst f f p) ∧
      chart d (pullback.snd g g q) = chart c (pullback.snd f f p) ∧
      (q ∈ D' ∨ q ∈ C')) := by
  classical
  by_cases hx : u ∈ (I (pullback.fst f f p)).asIdeal
  · have hx' := hx
    rw [arithmeticFixedAdjacentTargetCoordinates_eq_next_source
      hπ data m k hk i hi hiNext] at hx'
    by_cases hy : u ∈ (I (pullback.snd f f p)).asIdeal
    · have hy' := hy
      rw [arithmeticFixedAdjacentTargetCoordinates_eq_next_source
        hπ data m k hk i hi hiNext] at hy'
      obtain ⟨q, hq, he, hv, hw⟩ := arithmeticRetainedDouble_anyDepth_zero_coordinates
        hπ data node hgen m k hk (i + 1) (i + 1) hiNext hiNext
        (by omega) (by omega) p hs ht hx' hy'
      exact Or.inr (Or.inr (Or.inr ⟨q, hq, he,
        arithmeticTargetSelfDeep_punctured_cover node data m k hk (i + 1) hiNext
          (by omega) (by omega) q hv hw⟩))
    · let z := (pullbackSymmetry f f).hom p
      have hz : chart c (pullback.snd f f z) ∈ (s).smoothLocus := by
        rw [SchemePairSymmetryPoints.snd_apply]
        exact hs
      have hu : u ∉ (I (pullback.fst f f z)).asIdeal := by
        rw [SchemePairSymmetryPoints.fst_apply]
        exact hy
      have hv : u ∈ (arithmeticFixedAdjacentSourceCoordinates hπ data m k hk
          (i + 1) hiNext (pullback.snd f f z)).asIdeal := by
        rw [SchemePairSymmetryPoints.snd_apply]
        exact hx'
      obtain ⟨q, hq, he, ho⟩ := arithmeticRetainedSecond_zero_addition_target
        node data m k hk i (i + 1) hi hiNext (by omega) (by omega) (by omega) h2
        hgen (by omega) z hz hu hv
      rw [SchemePairSymmetryPoints.fst_apply] at hq
      rw [SchemePairSymmetryPoints.snd_apply] at he
      exact Or.inr (Or.inr (Or.inl ⟨q, hq, he, ho⟩))
  · by_cases hy : u ∈ (I (pullback.snd f f p)).asIdeal
    · have hy' := hy
      rw [arithmeticFixedAdjacentTargetCoordinates_eq_next_source
        hπ data m k hk i hi hiNext] at hy'
      obtain ⟨q, hq, he, ho⟩ := arithmeticRetainedSecond_zero_addition_target
        node data m k hk i (i + 1) hi hiNext (by omega) (by omega) (by omega) h2
        hgen (by omega) p ht hx hy'
      exact Or.inr (Or.inl ⟨q, hq, he, ho⟩)
    · exact Or.inl (arithmeticTargetSelfDeep_punctured_cover node data m k hk i hi
        (by omega) (by omega) p hx hy)

end FLT.Mazur.WeierstrassDividedDepth

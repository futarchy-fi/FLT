/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedZeroShortLocal

/-!
# Full creation-zero retained coverage starting at atlas stage two

Every smooth point of the entire original pair lifts to an actual formula
source. The mixed cases use the direct source/target unequal-depth output;
no horizontal puncture, tangent denominator or coefficient normalization
is assumed of the original pair.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticFixedAdjacentSourceCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i + 2 ≤ k)
  (hsum : (i + 1) + (i + 1) ≤ k) (hpre : 2 * (i + 1) < depth)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "e" => data ⟨i + 1,
  Nat.lt_succ_of_le ((Nat.le_succ (i + 1)).trans (hi.trans hk))⟩
local notation "c" => (Fin.succ ⟨k - i,
  Nat.lt_succ_of_le ((Nat.sub_le k i).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "f" => chart c ≫ s
local notation "I" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk i hi
local notation "u" => tensorCoord W (π ^ (0 + i)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2
local notation "O" => arithmeticFixedAdjacentPairOpen hπ data m k hk i hi f
local notation "D" => arithmeticRetainedDoubleOpen hπ data m k hk i i hi hi
local notation "X" => arithmeticRetainedZeroShortLocalSource node data m k hk i hi hsum hpre
local notation "inc" => arithmeticRetainedZeroShortLocalInclusion node data m k hk
  i hi hsum hpre

local instance arithmeticZeroShortLocalCover_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- All smooth zero-created pairs lift to one of the five actual output sources. -/
theorem arithmeticRetainedZeroShortLocal_exists (hz : i = 0)
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (p : (pullback f f : Scheme))
    (hs : chart c (pullback.fst f f p) ∈ (s).smoothLocus)
    (ht : chart c (pullback.snd f f p) ∈ (s).smoothLocus) :
    ∃ b, ∃ z : X b, inc b z = p := by
  classical
  by_cases hx : u ∈ (I (pullback.fst f f p)).asIdeal
  · by_cases hy : u ∈ (I (pullback.snd f f p)).asIdeal
    · let v : (D).toScheme := ⟨p, arithmeticRetainedDoubleOpen_anyDepth_zero_mem
        hπ data node hgen m k hk i i hi hi (by omega) (by omega) p hs ht hx hy⟩
      have hp := arithmeticRetainedDoubleTransfer_punctured hπ data m k hk i i hi hi v
      rcases arithmeticTargetSelfPreMiddle_punctured_cover node data m k hk i hi hsum hpre
        (arithmeticRetainedDoubleTransfer hπ data m k hk i i hi hi v) hp.1 hp.2 with hv | hv
      · exact ⟨.inr (.inr false), ⟨v, hv⟩, rfl⟩
      · exact ⟨.inr (.inr true), ⟨v, hv⟩, rfl⟩
    · let v : (O).toScheme := ⟨p, arithmeticFixedAdjacentPairOpen_zero_mem
        hπ data node hgen m k hk i hi f (by omega) p hs hx⟩
      have hv := arithmeticRetainedZeroShortSingleOpen_mem node data m k hk i hi
        (by omega) hz (by omega) v hy
      exact ⟨.inr (.inl false), ⟨v, hv⟩, rfl⟩
  · by_cases hy : u ∈ (I (pullback.snd f f p)).asIdeal
    · let z := (pullbackSymmetry f f).hom p
      have hs' : chart c (pullback.fst f f z) ∈ (s).smoothLocus := by
        rw [SchemePairSymmetryPoints.fst_apply]
        exact ht
      have hu : u ∈ (I (pullback.fst f f z)).asIdeal := by
        rw [SchemePairSymmetryPoints.fst_apply]
        exact hy
      let v : (O).toScheme := ⟨z, arithmeticFixedAdjacentPairOpen_zero_mem
        hπ data node hgen m k hk i hi f (by omega) z hs' hu⟩
      have hu' : u ∉ (I (pullback.snd f f ((O).ι v))).asIdeal := by
        change u ∉ (I (pullback.snd f f z)).asIdeal
        rw [SchemePairSymmetryPoints.snd_apply]
        exact hx
      have hv := arithmeticRetainedZeroShortSingleOpen_mem node data m k hk i hi
        (by omega) hz (by omega) v hu'
      refine ⟨.inr (.inl true), ⟨v, hv⟩, ?_⟩
      exact congrArg (fun morphism => morphism p) (Iso.hom_inv_id (pullbackSymmetry f f))
    · exact ⟨.inl (), ⟨p, arithmeticSourceSelfOriginalSmooth_zero_punctured
        node data m k hk i hi hz (by omega) p hx hy⟩, rfl⟩

/-- The five actual formula images cover the entire relatively smooth original pair. -/
theorem arithmeticRetainedZeroShortLocal_smooth_le (hz : i = 0)
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) :
    (pullback.fst f f ≫ chart c) ⁻¹ᵁ (s).smoothLocus ⊓
      (pullback.snd f f ≫ chart c) ⁻¹ᵁ (s).smoothLocus ≤ ⨆ b, (inc b).opensRange := by
  intro p hp
  obtain ⟨b, z, hb⟩ := arithmeticRetainedZeroShortLocal_exists
    node data m k hk i hi hsum hpre hz hgen p hp.1 hp.2
  exact (le_iSup (fun b => (inc b).opensRange) b) ⟨z, hb⟩

end FLT.Mazur.WeierstrassDividedDepth

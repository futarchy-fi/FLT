/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedEqualWiderReflectedLocal

/-!
# Full equal-retained coverage in the wider reflected mixed-input range

Every smooth point of the full original pair lifts to one of the ten actual
open sources. Both original inputs and the quotient coefficient morphism
remain unchanged; no abscissa puncture is required of the original pair.
For original creation depth r, the range is 3*r+2 ≤ node depth < 4*r+2.
The upper boundary is not included.
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
  (hlo : (i + 1) + 2 * (i + 2) ≤ depth) (hhi : depth < 2 * ((i + 1) + (i + 2)))
  (hstage : depth - 2 * (i + 1) ≤ k)
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
local notation "V" => arithmeticTargetSelfFlexiblePreMiddleOpen node data m k hk i hi
  (by omega) (by omega)
local notation "Z" => arithmeticTargetSelfReciprocalOpen node data m k hk i hi
local notation "O" => arithmeticFixedAdjacentPairOpen hπ data m k hk (i + 1) hiNext f
local notation "D" => arithmeticRetainedDoubleOpen hπ data m k hk
  (i + 1) (i + 1) hiNext hiNext
local notation "MC" => arithmeticRetainedSelfWiderReflectedMixedChart node data m k hk i hi hiNext
  (by omega) (by omega) (by omega)
local notation "MO" => arithmeticRetainedSelfWiderReflectedMixedOutput node data m k hk i hi hiNext
  (by omega) (by omega) (by omega)
local notation "TC" => arithmeticRetainedSelfFlexiblePreMiddleTransferChart node data m k hk
  (i + 1) hiNext (by omega) (by omega)
local notation "TO" => arithmeticRetainedSelfFlexiblePreMiddleTransferOutput node data m k hk
  (i + 1) hiNext (by omega) (by omega)
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

local notation "X" => arithmeticRetainedEqualWiderReflectedLocalSource node data m k hk i hi hiNext
  hlo hhi hstage
local notation "inc" => arithmeticRetainedEqualWiderReflectedLocalInclusion
  node data m k hk i hi hiNext hlo hhi hstage

local instance arithmeticEqualWiderReflectedLocalCover_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Each smooth original pair belongs to the image of an actual local output source. -/
theorem arithmeticRetainedEqualWiderReflectedLocal_exists
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (p : (pullback f f : Scheme))
    (hs : chart c (pullback.fst f f p) ∈ (s).smoothLocus)
    (ht : chart c (pullback.snd f f p) ∈ (s).smoothLocus) :
    ∃ b, ∃ z : X b, inc b z = p := by
  classical
  by_cases hx : u ∈ (I (pullback.fst f f p)).asIdeal
  · have hx' := hx
    rw [arithmeticFixedAdjacentTargetCoordinates_eq_next_source
      hπ data m k hk i hi hiNext] at hx'
    by_cases hy : u ∈ (I (pullback.snd f f p)).asIdeal
    · have hy' := hy
      rw [arithmeticFixedAdjacentTargetCoordinates_eq_next_source
        hπ data m k hk i hi hiNext] at hy'
      let v : (D).toScheme := ⟨p, arithmeticRetainedDoubleOpen_anyDepth_zero_mem
        hπ data node hgen m k hk (i + 1) (i + 1) hiNext hiNext
        (by omega) (by omega) p hs ht hx' hy'⟩
      have hp := arithmeticRetainedDoubleTransfer_punctured
        hπ data m k hk (i + 1) (i + 1) hiNext hiNext v
      rcases arithmeticTargetSelfFlexiblePreMiddle_punctured_cover node data m k hk (i + 1) hiNext
        (by omega) (by omega)
        (arithmeticRetainedDoubleTransfer hπ data m k hk
          (i + 1) (i + 1) hiNext hiNext v) hp.1 hp.2 with hv | hv
      · exact ⟨.inr (.inr false), ⟨v, hv⟩, rfl⟩
      · exact ⟨.inr (.inr true), ⟨v, hv⟩, rfl⟩
    · let v : (O).toScheme := ⟨p, arithmeticFixedAdjacentPairOpen_zero_mem
        hπ data node hgen m k hk (i + 1) hiNext f (by omega) p hs hx'⟩
      obtain ⟨b, hb⟩ := arithmeticRetainedSelfWiderReflectedMixedChart_covers
        node data m k hk i hi hiNext
        (by omega) (by omega) (by omega) v hy
      exact ⟨.inr (.inl (false, b)), ⟨v, hb⟩, rfl⟩
  · by_cases hy : u ∈ (I (pullback.snd f f p)).asIdeal
    · have hy' := hy
      rw [arithmeticFixedAdjacentTargetCoordinates_eq_next_source
        hπ data m k hk i hi hiNext] at hy'
      let z := (pullbackSymmetry f f).hom p
      have hz : chart c (pullback.fst f f z) ∈ (s).smoothLocus := by
        rw [SchemePairSymmetryPoints.fst_apply]
        exact ht
      have hu : u ∈ (arithmeticFixedAdjacentSourceCoordinates hπ data m k hk
          (i + 1) hiNext (pullback.fst f f z)).asIdeal := by
        rw [SchemePairSymmetryPoints.fst_apply]
        exact hy'
      let v : (O).toScheme := ⟨z, arithmeticFixedAdjacentPairOpen_zero_mem
        hπ data node hgen m k hk (i + 1) hiNext f (by omega) z hz hu⟩
      have hv : u ∉ (I (pullback.snd f f ((O).ι v))).asIdeal := by
        change u ∉ (I (pullback.snd f f z)).asIdeal
        rw [SchemePairSymmetryPoints.snd_apply]
        exact hx
      obtain ⟨b, hb⟩ := arithmeticRetainedSelfWiderReflectedMixedChart_covers
        node data m k hk i hi hiNext
        (by omega) (by omega) (by omega) v hv
      refine ⟨.inr (.inl (true, b)), ⟨v, hb⟩, ?_⟩
      exact congrArg (fun morphism => morphism p) (Iso.hom_inv_id (pullbackSymmetry f f))
    · rcases arithmeticTargetSelfFlexiblePreMiddle_punctured_cover node data m k hk i hi
        (by omega) (by omega) p hx hy with hv | hv
      · exact ⟨.inl false, ⟨p, hv⟩, rfl⟩
      · exact ⟨.inl true, ⟨p, hv⟩, rfl⟩

/-- The images of actual formula sources cover the whole relatively smooth input domain. -/
theorem arithmeticRetainedEqualWiderReflectedLocal_smooth_le
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) :
    (pullback.fst f f ≫ chart c) ⁻¹ᵁ (s).smoothLocus ⊓
      (pullback.snd f f ≫ chart c) ⁻¹ᵁ (s).smoothLocus ≤ ⨆ b, (inc b).opensRange := by
  intro p hp
  obtain ⟨b, z, hz⟩ := arithmeticRetainedEqualWiderReflectedLocal_exists
    node data m k hk i hi hiNext hlo hhi hstage hgen p hp.1 hp.2
  exact (le_iSup (fun b => (inc b).opensRange) b) ⟨z, hz⟩

end FLT.Mazur.WeierstrassDividedDepth

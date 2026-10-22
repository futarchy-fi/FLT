/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedAdjacentFactoredSumLocal

/-!
# Actual local outputs for adjacent retained pairs

Eleven actual domains handle the unshifted pair, either single transfer and
the double transfer. The first-only transfer uses the flexible self-pair
formulas because its two target creation depths coincide.
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
  (m k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i + 2 ≤ k)
  (hiNext : (i + 1) + 2 ≤ k) (hiLast : ((i + 1) + 1) + 2 ≤ k)
  (hdepth : 2 * ((i + 2) + ((i + 1) + 2)) < depth)
  (hsum : (i + 2) + ((i + 1) + 2) ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨i + 2, Nat.lt_succ_of_le (hi.trans hk)⟩
local notation "ej" => data ⟨(i + 1) + 2, Nat.lt_succ_of_le (hiNext.trans hk)⟩
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - ((i + 1) + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k ((i + 1) + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk (i + 1) hiNext

local notation "di" => data ⟨i + 1, by omega⟩
local notation "dj" => data ⟨(i + 1) + 1, by omega⟩
local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "v" => tensorCoord W (π ^ (0 + ((i + 1) + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2

local notation "index" => fun r : ℕ => (Fin.succ ⟨k - r,
  Nat.lt_succ_of_le ((Nat.sub_le k r).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "f" => chart c ≫ s
local notation "g" => chart d ≫ s

local notation "V" => arithmeticTargetFactoredSumOutputChart node data m k hk i (i + 1) hi hiNext
  (by omega) (by omega) (by omega)
local notation "SC" => arithmeticRetainedAdjacentSelfFlexibleTransferChart node data m k hk
  (i + 1) hiNext (by omega) (by omega)
local notation "SO" => arithmeticRetainedAdjacentSelfFlexibleTransferOutput node data m k hk
  (i + 1) hiNext (by omega) (by omega)
local notation "RC" => arithmeticRetainedSecondFactoredSumChart node data m k hk
  i ((i + 1) + 1) hi hiLast (by omega) (by omega) (by omega)
local notation "RO" => arithmeticRetainedSecondFactoredSumOutput node data m k hk
  i ((i + 1) + 1) hi hiLast (by omega) (by omega) (by omega)
local notation "DC" => arithmeticRetainedDoubleFactoredSumChart node data m k hk
  (i + 1) ((i + 1) + 1) hiNext hiLast (by omega) (by omega) (by omega)
local notation "DO" => arithmeticRetainedDoubleFactoredSumOutput node data m k hk
  (i + 1) ((i + 1) + 1) hiNext hiLast (by omega) (by omega) (by omega)
local notation "S" => arithmeticFixedAdjacentPairOpen hπ data m k hk (i + 1) hiNext g
local notation "T" => arithmeticFixedAdjacentPairOpen hπ data m k hk ((i + 1) + 1) hiLast f
local notation "D" => arithmeticRetainedDoubleOpen hπ data m k hk
  (i + 1) ((i + 1) + 1) hiNext hiLast
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

local notation "X" => arithmeticRetainedAdjacentFactoredSumLocalSource
  node data m k hk i hi hiNext hiLast hdepth hsum
local notation "inc" => arithmeticRetainedAdjacentFactoredSumLocalInclusion
  node data m k hk i hi hiNext hiLast hdepth hsum

local instance arithmeticAdjacentFactoredSumLocalCover_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Every smooth original pair lifts to an actual quotient-output source. -/
theorem arithmeticRetainedAdjacentFactoredSumLocal_exists
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (p : (pullback f g : Scheme))
    (hs : chart c (pullback.fst f g p) ∈ (s).smoothLocus)
    (ht : chart d (pullback.snd f g p) ∈ (s).smoothLocus) :
    ∃ b, ∃ z : X b, inc b z = p := by
  classical
  by_cases hx : u ∈ (I (pullback.fst f g p)).asIdeal
  · have hx' := hx
    rw [arithmeticFixedAdjacentTargetCoordinates_eq_next_source
      hπ data m k hk i hi hiNext] at hx'
    by_cases hy : v ∈ (J (pullback.snd f g p)).asIdeal
    · have hy' := hy
      rw [arithmeticFixedAdjacentTargetCoordinates_eq_next_source
        hπ data m k hk (i + 1) hiNext hiLast] at hy'
      let z : (D).toScheme := ⟨p, arithmeticRetainedDoubleOpen_anyDepth_zero_mem
        hπ data node hgen m k hk (i + 1) ((i + 1) + 1) hiNext hiLast
        (by omega) (by omega) p hs ht hx' hy'⟩
      obtain ⟨b, hb⟩ := arithmeticRetainedDoubleFactoredSumChart_covers node data m k hk
        (i + 1) ((i + 1) + 1) hiNext hiLast (by omega) (by omega) (by omega)
        (by omega) (by omega) z
      exact ⟨.inr (.inr (.inr b)), ⟨z, hb⟩, rfl⟩
    · let z : (S).toScheme := ⟨p, arithmeticFixedAdjacentPairOpen_zero_mem
        hπ data node hgen m k hk (i + 1) hiNext g (by omega) p hs hx'⟩
      obtain ⟨b, hb⟩ := arithmeticRetainedAdjacentSelfFlexibleTransferChart_covers
        node data m k hk (i + 1) hiNext (by omega) (by omega) z hy
      exact ⟨.inr (.inl b), ⟨z, hb⟩, rfl⟩
  · by_cases hy : v ∈ (J (pullback.snd f g p)).asIdeal
    · have hy' := hy
      rw [arithmeticFixedAdjacentTargetCoordinates_eq_next_source
        hπ data m k hk (i + 1) hiNext hiLast] at hy'
      let z := (pullbackSymmetry f g).hom p
      have hz : chart d (pullback.fst g f z) ∈ (s).smoothLocus := by
        rw [SchemePairSymmetryPoints.fst_apply]
        exact ht
      have hu : v ∈ (arithmeticFixedAdjacentSourceCoordinates hπ data m k hk
          ((i + 1) + 1) hiLast (pullback.fst g f z)).asIdeal := by
        rw [SchemePairSymmetryPoints.fst_apply]
        exact hy'
      let w : (T).toScheme := ⟨z, arithmeticFixedAdjacentPairOpen_zero_mem
        hπ data node hgen m k hk ((i + 1) + 1) hiLast f (by omega) z hz hu⟩
      have hw : u ∉ (I (pullback.snd g f ((T).ι w))).asIdeal := by
        change u ∉ (I (pullback.snd g f z)).asIdeal
        rw [SchemePairSymmetryPoints.snd_apply]
        exact hx
      obtain ⟨b, hb⟩ := arithmeticRetainedSecondFactoredSumChart_covers node data m k hk
        i ((i + 1) + 1) hi hiLast (by omega) (by omega) (by omega) (by omega) (by omega) w hw
      refine ⟨.inr (.inr (.inl b)), ⟨w, hb⟩, ?_⟩
      exact congrArg (fun morphism => morphism p) (Iso.hom_inv_id (pullbackSymmetry f g))
    · obtain ⟨b, hb⟩ := arithmeticTargetFactoredSumOutputChart_punctured
        node data m k hk i (i + 1) hi hiNext (by omega) (by omega) (by omega)
        (by omega) (by omega) p hx hy
      exact ⟨.inl b, ⟨p, hb⟩, rfl⟩

/-- The local source images cover the whole relatively smooth original pair. -/
theorem arithmeticRetainedAdjacentFactoredSumLocal_smooth_le
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) :
    (pullback.fst f g ≫ chart c) ⁻¹ᵁ (s).smoothLocus ⊓
      (pullback.snd f g ≫ chart d) ⁻¹ᵁ (s).smoothLocus ≤ ⨆ b, (inc b).opensRange := by
  intro p hp
  obtain ⟨b, z, hz⟩ := arithmeticRetainedAdjacentFactoredSumLocal_exists
    node data m k hk i hi hiNext hiLast hdepth hsum hgen p hp.1 hp.2
  exact (le_iSup (fun b => (inc b).opensRange) b) ⟨z, hz⟩

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedZeroAdjacentBoundaryLocal

/-!
# Creation-zero adjacent boundary pairs at final stage two

At node depth four or five, combine the direct opposite formula, two self
formulas after the earlier transfer, and four complete last-transfer sources.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticFixedAdjacentTargetCoordinates arithmeticFixedAdjacentSourceCoordinates
  arithmeticTensorAtlasMap globalTensorAtlasObject
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m : ℕ) (hk : 2 ≤ n)
  (hdepth : 4 ≤ depth) (hnear : depth ≤ 5)
local notation "k" => 2
local notation "hi" => (Nat.le_refl 2)
local notation "hj" => (Nat.le_refl 2)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨1, Nat.lt_succ_of_le ((Nat.le_trans
  (Nat.le_succ 1) hi).trans hk)⟩
local notation "ej" => data ⟨2, Nat.lt_succ_of_le hk⟩
local notation "c" => (Fin.succ ⟨k - 0,
  Nat.lt_succ_of_le ((Nat.sub_le k 0).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - 1,
  Nat.lt_succ_of_le ((Nat.sub_le k 1).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "I" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk 0 hi
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk 0 hj

local notation "u" => tensorCoord W (π ^ (0 + 0)) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "v" => tensorCoord W (π ^ (0 + 1)) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2

local notation "index" => fun r : ℕ => (Fin.succ ⟨k - r,
  Nat.lt_succ_of_le ((Nat.sub_le k r).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "f" => chart c ≫ s
local notation "g" => chart d ≫ s

local notation "V" => arithmeticSourceTargetOppositeOpen node data m k hk 0 0 hi hj
  (by omega) (by omega)
local notation "SC" => arithmeticRetainedAdjacentSelfFlexibleTransferChart node data m k hk
  0 hi (by omega) (by omega)
local notation "SO" => arithmeticRetainedAdjacentSelfFlexibleTransferOutput node data m k hk
  0 hi (by omega) (by omega)
local notation "MC" => arithmeticLastRetainedMixedZeroBoundaryChart node data m 1 hk
  0 (by omega) hdepth hnear
local notation "MO" => arithmeticLastRetainedMixedZeroBoundaryOutput node data m 1 hk
  0 (by omega) hdepth hnear
local notation "S" => arithmeticFixedAdjacentPairOpen hπ data m k hk 0 hi g
local notation "T" => arithmeticLastRetainedPairOpen node data m 1 hk f
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

local notation "X" => arithmeticLastRetainedZeroAdjacentBoundaryLocalSource
  node data m hk hdepth hnear
local notation "inc" => arithmeticLastRetainedZeroAdjacentBoundaryLocalInclusion
  node data m hk hdepth hnear
local notation "coords" => arithmeticLastRetainedIndexedCoordinates node data m 1 hk

local instance arithmeticLastRetainedZeroAdjacentBoundaryLocalCover_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Every smooth original pair reaches one of the complete local output sources. -/
theorem arithmeticLastRetainedZeroAdjacentBoundaryLocal_exists
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (p : (pullback f g : Scheme))
    (hs : chart c (pullback.fst f g p) ∈ (s).smoothLocus)
    (ht : chart d (pullback.snd f g p) ∈ (s).smoothLocus) :
    ∃ b, ∃ z : X b, inc b z = p := by
  classical
  have he : J = coords := by
    unfold arithmeticFixedAdjacentTargetCoordinates arithmeticLastRetainedIndexedCoordinates
    rfl
  by_cases hy : v ∈ (J (pullback.snd f g p)).asIdeal
  · let z := (pullbackSymmetry f g).hom p
    have hs' : chart d (pullback.fst g f z) ∈ (s).smoothLocus := by
      rw [SchemePairSymmetryPoints.fst_apply]
      exact ht
    have ht' : chart c (pullback.snd g f z) ∈ (s).smoothLocus := by
      rw [SchemePairSymmetryPoints.snd_apply]
      exact hs
    have hz : v ∈ (coords (pullback.fst g f z)).asIdeal := by
      rw [SchemePairSymmetryPoints.fst_apply, ← he]
      exact hy
    let w : (T).toScheme := ⟨z, arithmeticLastRetainedPairOpen_zero_mem
      node data m 1 hk f hgen hdepth z hs' hz⟩
    obtain ⟨b, hb⟩ := arithmeticLastRetainedMixedZeroBoundaryChart_covers
      node data m 1 hk 0 (by omega) hdepth hnear hgen rfl w hs' ht'
    refine ⟨.inr (.inr b), ⟨w, hb⟩, ?_⟩
    exact congrArg (fun morphism => morphism p) (Iso.hom_inv_id (pullbackSymmetry f g))
  · by_cases hx : u ∈ (I (pullback.fst f g p)).asIdeal
    · let w : (S).toScheme := ⟨p, arithmeticFixedAdjacentPairOpen_zero_mem
        hπ data node hgen m k hk 0 hi g (by omega) p hs hx⟩
      obtain ⟨b, hb⟩ := arithmeticRetainedAdjacentSelfFlexibleTransferChart_covers node data m k hk
        0 hi (by omega) (by omega) w hy
      exact ⟨.inr (.inl b), ⟨w, hb⟩, rfl⟩
    · exact ⟨.inl (), ⟨p, arithmeticSourceTargetOpposite_zero_le_middle_mem
        node data m k hk 0 0 hi hj (by omega) (by omega) rfl (by omega) p hx hy⟩, rfl⟩

/-- The genuine local images cover the entire relatively smooth original pair. -/
theorem arithmeticLastRetainedZeroAdjacentBoundaryLocal_smooth_le
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) :
    (pullback.fst f g ≫ chart c) ⁻¹ᵁ (s).smoothLocus ⊓
      (pullback.snd f g ≫ chart d) ⁻¹ᵁ (s).smoothLocus ≤ ⨆ b, (inc b).opensRange := by
  intro p hp
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedZeroAdjacentBoundaryLocal_exists
    node data m hk hdepth hnear hgen p hp.1 hp.2
  exact (le_iSup (fun b => (inc b).opensRange) b) ⟨z, hz⟩

end FLT.Mazur.WeierstrassDividedDepth

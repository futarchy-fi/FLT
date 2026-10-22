/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedAdjacentOddLocal

/-!
# Full local outputs for adjacent last-retained odd pairs

Combine unshifted formulas, the full self cover after transfer, and the complete
last-transfer incidence cover. The latter also contains the double-zero case.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticFixedAdjacentTargetCoordinates arithmeticTensorAtlasMap globalTensorAtlasObject
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m i : ℕ) (hk : i + 3 ≤ n) (hodd : depth = 2 * (i + 3) + 1)
local notation "j" => i + 1
local notation "k" => i + 3
local notation "hi" => (by omega : i + 2 ≤ k)
local notation "hj" => (by omega : j + 2 ≤ k)
local notation "hiNext" => (by omega : (i + 1) + 2 ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨i + 2, Nat.lt_succ_of_le ((hi).trans hk)⟩
local notation "ej" => data ⟨j + 2, Nat.lt_succ_of_le ((hj).trans hk)⟩
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

local notation "V" => arithmeticTargetFlexiblePreMiddleChart node data m k hk i j hi hj
  (by omega) (by omega) (by omega)
local notation "SC" => arithmeticLastRetainedAdjacentOddTransferChart node data m i hk hodd
local notation "SO" => arithmeticLastRetainedAdjacentOddTransferOutput node data m i hk hodd
local notation "MC" => arithmeticLastRetainedMixedBoundaryChart node data m (j + 1) hk
  (i + 1) (by omega) (by omega) (by omega)
local notation "MO" => arithmeticLastRetainedMixedBoundaryOutput node data m (j + 1) hk
  (i + 1) (by omega) (by omega) (by omega)
local notation "S" => arithmeticFixedAdjacentPairOpen hπ data m k hk (i + 1) hiNext g
local notation "T" => arithmeticLastRetainedPairOpen node data m (j + 1) hk f
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

local notation "X" => arithmeticLastRetainedAdjacentOddLocalSource
  node data m i hk hodd
local notation "inc" => arithmeticLastRetainedAdjacentOddLocalInclusion
  node data m i hk hodd
local notation "coords" => arithmeticLastRetainedIndexedCoordinates node data m (j + 1) hk

local instance arithmeticLastRetainedAdjacentOddLocalCover_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Every smooth original pair reaches one of the complete local output sources. -/
theorem arithmeticLastRetainedAdjacentOddLocal_exists
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
      node data m (j + 1) hk f hgen (by omega) z hs' hz⟩
    obtain ⟨b, hb⟩ := arithmeticLastRetainedMixedBoundaryChart_covers
      node data m (j + 1) hk (i + 1) (by omega) (by omega) (by omega) hgen (by omega) w hs' ht'
    refine ⟨.inr (.inr b), ⟨w, hb⟩, ?_⟩
    exact congrArg (fun morphism => morphism p) (Iso.hom_inv_id (pullbackSymmetry f g))
  · by_cases hx : u ∈ (I (pullback.fst f g p)).asIdeal
    · have hx' := hx
      rw [arithmeticFixedAdjacentTargetCoordinates_eq_next_source
        hπ data m k hk i hi hiNext] at hx'
      let w : (S).toScheme := ⟨p, arithmeticFixedAdjacentPairOpen_zero_mem
        hπ data node hgen m k hk (i + 1) hiNext g (by omega) p hs hx'⟩
      obtain ⟨b, hb⟩ := arithmeticLastRetainedAdjacentOddTransferChart_covers
        node data m i hk hodd hgen w hs ht
      exact ⟨.inr (.inl b), ⟨w, hb⟩, rfl⟩
    · obtain ⟨b, hb⟩ := arithmeticTargetFlexiblePreMiddleChart_punctured
        node data m k hk i j hi hj (by omega) (by omega) (by omega)
        (by omega) p hx hy
      exact ⟨.inl b, ⟨p, hb⟩, rfl⟩

/-- The twenty-one genuine images cover the entire relatively smooth original pair. -/
theorem arithmeticLastRetainedAdjacentOddLocal_smooth_le
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) :
    (pullback.fst f g ≫ chart c) ⁻¹ᵁ (s).smoothLocus ⊓
      (pullback.snd f g ≫ chart d) ⁻¹ᵁ (s).smoothLocus ≤ ⨆ b, (inc b).opensRange := by
  intro p hp
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedAdjacentOddLocal_exists
    node data m i hk hodd hgen p hp.1 hp.2
  exact (le_iSup (fun b => (inc b).opensRange) b) ⟨z, hz⟩

end FLT.Mazur.WeierstrassDividedDepth

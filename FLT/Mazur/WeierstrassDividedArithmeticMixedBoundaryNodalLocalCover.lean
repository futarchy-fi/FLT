/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedBoundaryNodalLocal

/-!
# Local sources for the full retained/terminal boundary pair

Combine unshifted normalized formulas and the genuine adjacent incidence
sources. Every source embeds openly in the unchanged full arithmetic pair
and has a constructed quotient output with its full coefficient identity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  arithmeticRetainedTensorIso olderSuccessiveTensorAtlasIso finiteTensorAtlasObject
  arithmeticFixedAdjacentPairOpen arithmeticFixedAdjacentPairTransfer
  arithmeticTensorAtlasMap globalTensorAtlasObject
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (k : ℕ) (hk : k + 2 ≤ j)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "a" => (Fin.succ ⟨j - k,
  Nat.lt_succ_of_le ((Nat.sub_le j k).trans (Nat.le_succ j))⟩ : Fin (j + 3))
local notation "b" => (Fin.succ ⟨j - (k + 1), by omega⟩ : Fin (j + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O 1).ι ≫ chart 1 ≫ s
local notation "f" => chart a ≫ s
local notation "f'" => chart b ≫ s
local notation "g" => chart 1 ≫ s
local notation "B" => arithmeticFixedAdjacentPairOpen hπ data m j hj k hk g
local notation "transfer" => arithmeticFixedAdjacentPairTransfer hπ data m j hj k hk g
local notation "D" => arithmeticAdjacentMixedNodalSmoothOpen node data m j hj k hk
variable (hdepth : 2 * j ≤ depth) (hnear : depth ≤ k + 2 * j)
local notation "E" => arithmeticMixedNodalReflectedChart
  node data m j hj k (by omega) hdepth hnear
local notation "C" => arithmeticAdjacentMixedNodalChart
  node data m j hj k hk hdepth (by omega)
local notation "inc" => arithmeticSmoothPairInclusion hπ data m j hj a 1

local notation "X" => arithmeticMixedBoundaryNodalLocalSource node data m j hj k hk hdepth hnear
local notation "J" => arithmeticMixedBoundaryNodalLocalInclusion
  node data m j hj k hk hdepth hnear
local notation "next" => data ⟨k + 1,
  Nat.lt_succ_of_le ((Nat.le_succ (k + 1)).trans (hk.trans hj))⟩
local notation "I" => arithmeticFixedAdjacentSourceCoordinates hπ data m j hj k hk
local notation "u" => WeierstrassSuccessiveX.tensorCoord W (π ^ (0 + k)) π
  (next).b3 (next).b4 (next).b6 Q 2

local instance arithmeticMixedBoundaryNodalLocalCover_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data j hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Every full smooth retained/terminal pair reaches a genuine local output source. -/
theorem arithmeticMixedBoundaryNodalLocal_exists
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hk0 : 0 < k)
    (p : (pullback f g : Scheme))
    (hs : chart a (pullback.fst f g p) ∈ (s).smoothLocus)
    (ht : chart 1 (pullback.snd f g p) ∈ (s).smoothLocus) :
    ∃ c, ∃ z : X c, J c z = p := by
  classical
  have hs' := (arithmeticAtlasSmoothOpen_mem_relative hπ data m j hj a _).mpr hs
  have ht' := (arithmeticAtlasSmoothOpen_mem_relative hπ data m j hj 1 _).mpr ht
  by_cases hx : u ∈ (I (pullback.fst f g p)).asIdeal
  · let v : (B).toScheme := ⟨p, arithmeticFixedAdjacentPairOpen_zero_mem
      hπ data node hgen m j hj k hk g (by omega) p hs hx⟩
    let w : (D).toScheme := ⟨v, by
      change pullback.fst f g p ∈ O a ∧ pullback.snd f g p ∈ O 1
      exact ⟨hs', ht'⟩⟩
    obtain ⟨c, hc⟩ := arithmeticAdjacentMixedNodalChart_exists
      node data m j hj k hk hdepth (by omega) w
    exact ⟨(true, c), ⟨w, hc⟩, rfl⟩
  · obtain ⟨v, hv⟩ := arithmeticSmoothPairInclusion_exists hπ data m j hj a 1 p hs ht
    have he : (O a).ι (pullback.fst fa fb v) = pullback.fst f g p := by
      rw [← hv]
      exact congrArg (fun morphism => morphism v)
        (arithmeticSmoothPairInclusion_first hπ data m j hj a 1).symm
    obtain ⟨c, hc⟩ := arithmeticMixedNodalReflectedChart_near
      node data m j hj k (by omega) hdepth hnear hk0 v (by
        intro hz
        apply hx
        have hz' := (arithmeticMixedFormulaInput_x_iff
          hπ data m j hj k j (by omega) le_rfl v).mp hz
        change u ∈ (I ((O a).ι (pullback.fst fa fb v))).asIdeal at hz'
        rw [he] at hz'
        exact hz')
    exact ⟨(false, c), ⟨v, hc⟩, hv⟩

/-- The six actual source images exhaust the entire original smooth-pair open. -/
theorem arithmeticMixedBoundaryNodalLocal_smooth_le
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hk0 : 0 < k) :
    (pullback.fst f g ≫ chart a) ⁻¹ᵁ (s).smoothLocus ⊓
      (pullback.snd f g ≫ chart 1) ⁻¹ᵁ (s).smoothLocus ≤ ⨆ c, (J c).opensRange := by
  intro p hp
  obtain ⟨c, z, hz⟩ := arithmeticMixedBoundaryNodalLocal_exists
    node data m j hj k hk hdepth hnear hgen hk0 p hp.1 hp.2
  exact (le_iSup (fun c => (J c).opensRange) c) ⟨z, hz⟩

end FLT.Mazur.WeierstrassDividedDepth

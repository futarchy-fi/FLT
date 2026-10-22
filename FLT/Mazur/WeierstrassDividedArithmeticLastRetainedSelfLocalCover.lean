/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedSelfLocal

/-!
# Full smooth coverage at the equal last-retained middle boundary

Split by the two original horizontal coordinates. Double zero uses the full
terminal self-law; either single zero uses a transferred mixed source.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m i : ℕ) (hi : i + 2 ≤ n)
local notation "j" => i + 1
local notation "hj" => hi
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "a" => retainedOlderFormulaIndex (j + 1) j (Nat.lt_succ_self j)
local notation "chart" => arithmeticTensorAtlasMap hπ data m (j + 1) hj
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 1) hj m
local notation "old" => finiteArithmeticNewestTensorChart hπ data m j hj
local notation "next" => finiteArithmeticDividedTensorChart hπ data m (j + 1) hj
local notation "E" => finiteDividedTensorAtlasIso hπ data Q (j + 1) hj
local notation "f" => chart a ≫ s
local notation "f₀" => old ≫ s
local notation "f'" => next ≫ s
local notation "g'" => chart 1 ≫ s
local notation "coords" => arithmeticLastRetainedIndexedCoordinates node data m j hj



variable (hm : 2 * (i + 2) = depth)
local notation "V" => arithmeticLastRetainedSelfPuncturedChart node data m i hi hm
local notation "MC" => arithmeticLastRetainedSelfMixedChart node data m j hj
local notation "O" => arithmeticLastRetainedPairOpen node data m j hj f
local notation "O₂" => arithmeticLastRetainedDoubleOpen node data m j hj
local notation "D₂" => arithmeticLastRetainedDoubleMiddleSmoothOpen node data m j hj
local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

local notation "X" => arithmeticLastRetainedSelfLocalSource node data m i hi hm
local notation "inc" => arithmeticLastRetainedSelfLocalInclusion node data m i hi hm
local notation "e" => data ⟨i + 2, Nat.lt_succ_of_le hi⟩
local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π (e).b3 (e).b4 (e).b6 Q 2

local instance arithmeticLastRetainedSelfLocalCover_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data (j + 1) hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Every smooth original equal-retained pair reaches a complete local output source. -/
theorem arithmeticLastRetainedSelfLocal_exists
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (p : (pullback f f : Scheme))
    (hs : chart a (pullback.fst f f p) ∈ (s).smoothLocus)
    (ht : chart a (pullback.snd f f p) ∈ (s).smoothLocus) :
    ∃ b, ∃ z : X b, inc b z = p := by
  classical
  by_cases hx : u ∈ (coords (pullback.fst f f p)).asIdeal
  · by_cases hy : u ∈ (coords (pullback.snd f f p)).asIdeal
    · obtain ⟨z, hz⟩ := arithmeticLastRetainedDoubleMiddleSmoothOpen_zero_exists
        node data m j hj hgen hm p hs ht hx hy
      exact ⟨.inr (.inr ()), z, hz⟩
    · let v : (O).toScheme := ⟨p,
        arithmeticLastRetainedPairOpen_zero_mem node data m j hj f hgen hm.le p hs hx⟩
      obtain ⟨b, hb⟩ := arithmeticLastRetainedSelfMixedChart_covers
        node data m j hj hm hgen v hs ht
      exact ⟨.inr (.inl (false, b)), ⟨v, hb⟩, rfl⟩
  · by_cases hy : u ∈ (coords (pullback.snd f f p)).asIdeal
    · let z := (pullbackSymmetry f f).hom p
      have hs' : chart a (pullback.fst f f z) ∈ (s).smoothLocus := by
        rw [SchemePairSymmetryPoints.fst_apply]
        exact ht
      have ht' : chart a (pullback.snd f f z) ∈ (s).smoothLocus := by
        rw [SchemePairSymmetryPoints.snd_apply]
        exact hs
      have hz : u ∈ (coords (pullback.fst f f z)).asIdeal := by
        rw [SchemePairSymmetryPoints.fst_apply]
        exact hy
      let v : (O).toScheme := ⟨z,
        arithmeticLastRetainedPairOpen_zero_mem node data m j hj f hgen hm.le z hs' hz⟩
      obtain ⟨b, hb⟩ := arithmeticLastRetainedSelfMixedChart_covers
        node data m j hj hm hgen v hs' ht'
      refine ⟨.inr (.inl (true, b)), ⟨v, hb⟩, ?_⟩
      exact congrArg (fun morphism => morphism p) (Iso.hom_inv_id (pullbackSymmetry f f))
    · obtain ⟨b, hb⟩ := arithmeticLastRetainedSelfPuncturedChart_covers
        node data m i hi hm p hx hy
      exact ⟨.inl b, ⟨p, hb⟩, rfl⟩

/-- The seven actual images cover the entire relatively smooth original pair domain. -/
theorem arithmeticLastRetainedSelfLocal_smooth_le
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) :
    (pullback.fst f f ≫ chart a) ⁻¹ᵁ (s).smoothLocus ⊓
      (pullback.snd f f ≫ chart a) ⁻¹ᵁ (s).smoothLocus ≤ ⨆ b, (inc b).opensRange := by
  intro p hp
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedSelfLocal_exists
    node data m i hi hm hgen p hp.1 hp.2
  exact (le_iSup (fun b => (inc b).opensRange) b) ⟨z, hz⟩

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticStageOneOutputCovers

/-!
# Whole smooth stage-one test domains have quotient output covers

An arbitrary scheme with two actual chart inputs restricts to their complete
simultaneous smooth preimage. Pulling back the constructed pair cover retains
the original test-scheme coefficient morphism, including all nilpotents.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m : ℕ) (hi : 1 ≤ n)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "base" => finiteGlobalStructure hπ data 1 hi
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m 1 hi
local notation "s" => finiteGlobalArithmeticStructure hπ data 1 hi m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q 1 hi

variable (hgen : IsLocalRing.maximalIdeal R = ideal R π)
  (hd : depth = 2 ∨ depth = 3)
include hgen hd


/-- Every whole simultaneous smooth test domain has actual arithmetic output charts. -/
theorem arithmeticStageOneTestOutputCover (a b : Fin 4) {T : Scheme}
    (x : T ⟶ globalTensorAtlasObject hπ data Q 1 hi a)
    (y : T ⟶ globalTensorAtlasObject hπ data Q 1 hi b)
    (h : x ≫ chart a ≫ s = y ≫ chart b ≫ s) :
    ∃ (C : (arithmeticAtlasTestOpen hπ data m 1 hi a b x y).toScheme.OpenCover.{0})
      (out : (i : C.I₀) → C.X i ⟶ pullback q t),
      ∀ i, out i ≫ pullback.fst q t = C.f i ≫
        (arithmeticAtlasTestOpen hπ data m 1 hi a b x y).ι ≫ x ≫ chart a ≫ s := by
  obtain ⟨C, out, hc⟩ := arithmeticStageOnePairOutputCover node data m hi hgen hd a b
  obtain ⟨D, output, he⟩ := schemeQuotientOutputCover_pullback (pullback.fst q t)
    (pullback.fst ((O a).ι ≫ chart a ≫ s) ((O b).ι ≫ chart b ≫ s) ≫
      (O a).ι ≫ chart a ≫ s)
    (arithmeticAtlasTestPair hπ data m 1 hi a b x y h) C out hc
  refine ⟨D, output, ?_⟩
  intro i
  rw [he, arithmeticAtlasTestPair_first_assoc]

/-- The same local outputs retain the full second original coefficient morphism. -/
theorem arithmeticStageOneTestOutputCover_both (a b : Fin 4) {T : Scheme}
    (x : T ⟶ globalTensorAtlasObject hπ data Q 1 hi a)
    (y : T ⟶ globalTensorAtlasObject hπ data Q 1 hi b)
    (h : x ≫ chart a ≫ s = y ≫ chart b ≫ s) :
    ∃ (C : (arithmeticAtlasTestOpen hπ data m 1 hi a b x y).toScheme.OpenCover.{0})
      (out : (i : C.I₀) → C.X i ⟶ pullback q t),
      ∀ i, (out i ≫ pullback.fst q t = C.f i ≫
        (arithmeticAtlasTestOpen hπ data m 1 hi a b x y).ι ≫ x ≫ chart a ≫ s) ∧
        (out i ≫ pullback.fst q t = C.f i ≫
        (arithmeticAtlasTestOpen hπ data m 1 hi a b x y).ι ≫ y ≫ chart b ≫ s) := by
  obtain ⟨C, out, hc⟩ := arithmeticStageOneTestOutputCover node data m hi hgen hd a b x y h
  exact ⟨C, out, fun i => ⟨hc i, by rw [hc, h]⟩⟩

end FLT.Mazur.WeierstrassDividedDepth

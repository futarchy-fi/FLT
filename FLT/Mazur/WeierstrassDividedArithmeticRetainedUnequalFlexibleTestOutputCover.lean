/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedUnequalFlexibleOutputCover
public import FLT.Mazur.WeierstrassDividedArithmeticAtlasTestPair

/-!
# Test domains for positive unequal retained inputs at smaller stages

Restrict arbitrary indexed test inputs to their entire simultaneous smooth
preimage. The actual output cover retains both original coefficient maps.
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
  (m k : ℕ) (hk : k ≤ n) (i j : ℕ) (hlt : i < j)
  (hpre : 2 * (j + 2) < depth)
  (hstage : arithmeticFlexiblePairStage i j depth ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q k hk
local notation "a" => retainedOlderFormulaIndex k (i + 1)
  (by have := ((arithmeticFlexiblePairStage_le_iff i j depth k).mp hstage).1; omega)
local notation "b" => retainedOlderFormulaIndex k (j + 1)
  (by have := ((arithmeticFlexiblePairStage_le_iff i j depth k).mp hstage).1; omega)
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s
variable (hgen : IsLocalRing.maximalIdeal R = ideal R π)
include hlt hpre hstage hgen

/-- Whole compatible test schemes inherit the constructed quotient output cover. -/
theorem arithmeticRetainedUnequalFlexibleTestOutputCover {T : Scheme}
    (x : T ⟶ globalTensorAtlasObject hπ data Q k hk a)
    (y : T ⟶ globalTensorAtlasObject hπ data Q k hk b)
    (h : x ≫ chart a ≫ s = y ≫ chart b ≫ s) :
    ∃ (C : (arithmeticAtlasTestOpen hπ data m k hk a b x y).toScheme.OpenCover.{0})
      (out : (r : C.I₀) → C.X r ⟶ pullback q t),
      ∀ r, (out r ≫ pullback.fst q t = C.f r ≫
        (arithmeticAtlasTestOpen hπ data m k hk a b x y).ι ≫ x ≫ chart a ≫ s) ∧
        (out r ≫ pullback.fst q t = C.f r ≫
        (arithmeticAtlasTestOpen hπ data m k hk a b x y).ι ≫ y ≫ chart b ≫ s) := by
  obtain ⟨C, out, hc⟩ := arithmeticRetainedUnequalFlexibleOutputCover
    node data m k hk i j hlt hpre hstage hgen
  obtain ⟨D, output, he⟩ := schemeQuotientOutputCover_pullback (pullback.fst q t)
    (pullback.fst fa fb ≫ fa)
    (arithmeticAtlasTestPair hπ data m k hk a b x y h) C out hc
  refine ⟨D, output, fun r => ?_⟩
  have hr : output r ≫ pullback.fst q t = D.f r ≫
      (arithmeticAtlasTestOpen hπ data m k hk a b x y).ι ≫ x ≫ chart a ≫ s := by
    rw [he, arithmeticAtlasTestPair_first_assoc]
  exact ⟨hr, by rw [hr, h]⟩

/-- Reversed indexed inputs retain both full coefficient maps on the same smooth test domain. -/
theorem arithmeticRetainedUnequalFlexibleReversedTestOutputCover {T : Scheme}
    (x : T ⟶ globalTensorAtlasObject hπ data Q k hk b)
    (y : T ⟶ globalTensorAtlasObject hπ data Q k hk a)
    (h : x ≫ chart b ≫ s = y ≫ chart a ≫ s) :
    ∃ (C : (arithmeticAtlasTestOpen hπ data m k hk b a x y).toScheme.OpenCover.{0})
      (out : (r : C.I₀) → C.X r ⟶ pullback q t),
      ∀ r, (out r ≫ pullback.fst q t = C.f r ≫
        (arithmeticAtlasTestOpen hπ data m k hk b a x y).ι ≫ x ≫ chart b ≫ s) ∧
        (out r ≫ pullback.fst q t = C.f r ≫
        (arithmeticAtlasTestOpen hπ data m k hk b a x y).ι ≫ y ≫ chart a ≫ s) := by
  obtain ⟨C, out, hc⟩ := arithmeticRetainedUnequalFlexibleReversedOutputCover
    node data m k hk i j hlt hpre hstage hgen
  obtain ⟨D, output, he⟩ := schemeQuotientOutputCover_pullback (pullback.fst q t)
    (pullback.fst fb fa ≫ fb)
    (arithmeticAtlasTestPair hπ data m k hk b a x y h) C out hc
  refine ⟨D, output, fun r => ?_⟩
  have hr : output r ≫ pullback.fst q t = D.f r ≫
      (arithmeticAtlasTestOpen hπ data m k hk b a x y).ι ≫ x ≫ chart b ≫ s := by
    rw [he, arithmeticAtlasTestPair_first_assoc]
  exact ⟨hr, by rw [hr, h]⟩

end FLT.Mazur.WeierstrassDividedDepth

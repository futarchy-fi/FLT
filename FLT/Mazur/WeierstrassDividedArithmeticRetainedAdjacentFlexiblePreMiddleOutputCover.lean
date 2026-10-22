/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedAdjacentFlexiblePreMiddleLocalCover
public import FLT.Mazur.WeierstrassDividedArithmeticSmoothPairSourceCover
public import FLT.Mazur.SchemeQuotientOutputCover
public import FLT.Mazur.WeierstrassDividedArithmeticFlexibleStageBounds

/-!
# Whole quotient covers at flexible stages for adjacent inputs

The four transfer choices cover the relative product of smooth input charts.
The final stage contains the next input charts and the actual sum/reflected
output depths; it need not contain the larger unreflected output depths.
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
  (m k : ℕ) (hk : k ≤ n) (i : ℕ)
  (hpre : 2 * (i + 3) < depth)
  (hstage : arithmeticFlexiblePairStage i (i + 1) depth ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q k hk
local notation "a" => retainedOlderFormulaIndex k (i + 1)
  (by have := ((arithmeticFlexiblePairStage_le_iff i (i + 1) depth k).mp hstage).1; omega)
local notation "b" => retainedOlderFormulaIndex k (i + 2)
  (by have := ((arithmeticFlexiblePairStage_le_iff i (i + 1) depth k).mp hstage).1; omega)
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s
variable (hgen : IsLocalRing.maximalIdeal R = ideal R π)
include hpre hstage hgen

/-- The eleven genuine sources cover the entire smooth adjacent product. -/
theorem arithmeticRetainedAdjacentFlexiblePreMiddleOutputCover :
    ∃ (C : (pullback fa fb : Scheme).OpenCover.{0})
      (out : (j : C.I₀) → C.X j ⟶ pullback q t),
      ∀ j, out j ≫ pullback.fst q t = C.f j ≫ pullback.fst fa fb ≫ fa := by
  have hb := (arithmeticFlexiblePairStage_le_iff i (i + 1) depth k).mp hstage
  have hi : i + 2 ≤ k := by omega
  have hiNext : i + 3 ≤ k := by omega
  have hiLast : i + 4 ≤ k := by omega
  have ho : max (min (2 * i + 3) (depth - (2 * i + 3)))
      (max (min (2 * i + 4) (depth - (2 * i + 4)))
        (min (2 * i + 5) (depth - (2 * i + 5)))) ≤ k := by omega
  exact arithmeticSmoothPairSource_outputCover hπ data m k hk a b
    (arithmeticRetainedAdjacentFlexiblePreMiddleLocalSource
      node data m k hk i hi hiNext hiLast hpre ho)
    (arithmeticRetainedAdjacentFlexiblePreMiddleLocalInclusion
      node data m k hk i hi hiNext hiLast hpre ho)
    (arithmeticRetainedAdjacentFlexiblePreMiddleLocal_exists
      node data m k hk i hi hiNext hiLast hpre ho hgen)
    (arithmeticRetainedAdjacentFlexiblePreMiddleLocalOutput
      node data m k hk i hi hiNext hiLast hpre ho)
    (arithmeticRetainedAdjacentFlexiblePreMiddleLocalOutput_base
      node data m k hk i hi hiNext hiLast hpre ho)

/-- Exchanging the full inputs preserves coverage and the entire quotient coefficient map. -/
theorem arithmeticRetainedAdjacentFlexiblePreMiddleReversedOutputCover :
    ∃ (C : (pullback fb fa : Scheme).OpenCover.{0})
      (out : (j : C.I₀) → C.X j ⟶ pullback q t),
      ∀ j, out j ≫ pullback.fst q t = C.f j ≫ pullback.fst fb fa ≫ fb := by
  obtain ⟨C, out, h⟩ := arithmeticRetainedAdjacentFlexiblePreMiddleOutputCover
    node data m k hk i hpre hstage hgen
  exact schemeQuotientOutputCover_swap (pullback.fst q t) fa fb C out h

end FLT.Mazur.WeierstrassDividedDepth

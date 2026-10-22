/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedAdjacentFlexibleLocalCover
public import FLT.Mazur.WeierstrassDividedArithmeticSmoothPairSourceCover
public import FLT.Mazur.SchemeQuotientOutputCover

/-!
# Full smooth adjacent covers beyond the exact boundary depths

The source construction gives whole quotient outputs in both input orders.
The explicit incomplete-stage range is nonempty starting at creations three
and four, final stage five, and node depth twelve.
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
  (m i : ℕ) (hk : i + 3 ≤ n) (hdepth : 2 * (i + 3) < depth)
  (hnear : depth ≤ (i + 1) + 2 * (i + 3))
  (hsum : min (2 * i + 3) (depth - (2 * i + 3)) ≤ i + 3)
  (hself : min (2 * (i + 2)) (depth - 2 * (i + 2)) ≤ i + 3)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "base" => finiteGlobalStructure hπ data (i + 3) hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m (i + 3) hk
local notation "s" => finiteGlobalArithmeticStructure hπ data (i + 3) hk m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q (i + 3) hk
local notation "a" => retainedOlderFormulaIndex (i + 3) (i + 1) (by omega)
local notation "b" => retainedOlderFormulaIndex (i + 3) (i + 2) (by omega)
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s
variable (hgen : IsLocalRing.maximalIdeal R = ideal R π)
include hdepth hnear hsum hself hgen

/-- The eleven genuine sources cover the entire smooth adjacent product. -/
theorem arithmeticLastRetainedAdjacentFlexibleOutputCover :
    ∃ (C : (pullback fa fb : Scheme).OpenCover.{0})
      (out : (j : C.I₀) → C.X j ⟶ pullback q t),
      ∀ j, out j ≫ pullback.fst q t = C.f j ≫ pullback.fst fa fb ≫ fa := by
  exact arithmeticSmoothPairSource_outputCover hπ data m (i + 3) hk a b
    (arithmeticLastRetainedAdjacentFlexibleLocalSource
      node data m i hk hdepth hnear hsum hself)
    (arithmeticLastRetainedAdjacentFlexibleLocalInclusion
      node data m i hk hdepth hnear hsum hself)
    (arithmeticLastRetainedAdjacentFlexibleLocal_exists
      node data m i hk hdepth hnear hsum hself hgen)
    (arithmeticLastRetainedAdjacentFlexibleLocalOutput
      node data m i hk hdepth hnear hsum hself)
    (arithmeticLastRetainedAdjacentFlexibleLocalOutput_base
      node data m i hk hdepth hnear hsum hself)

/-- Exchanging the full inputs preserves coverage and the entire quotient coefficient map. -/
theorem arithmeticLastRetainedAdjacentFlexibleReversedOutputCover :
    ∃ (C : (pullback fb fa : Scheme).OpenCover.{0})
      (out : (j : C.I₀) → C.X j ⟶ pullback q t),
      ∀ j, out j ≫ pullback.fst q t = C.f j ≫ pullback.fst fb fa ≫ fb := by
  obtain ⟨C, out, h⟩ := arithmeticLastRetainedAdjacentFlexibleOutputCover
    node data m i hk hdepth hnear hsum hself hgen
  exact schemeQuotientOutputCover_swap (pullback.fst q t) fa fb C out h

omit hdepth hnear hsum hself in
/-- A nonempty range strictly beyond both previously covered exact boundary depths. -/
theorem arithmeticLastRetainedAdjacentBeyondBoundaryOutputCover
    (hlo : 2 * (i + 3) + 2 ≤ depth) (hhi : depth ≤ 3 * i + 6) :
    ∃ (C : (pullback fa fb : Scheme).OpenCover.{0})
      (out : (j : C.I₀) → C.X j ⟶ pullback q t),
      ∀ j, out j ≫ pullback.fst q t = C.f j ≫ pullback.fst fa fb ≫ fa := by
  exact arithmeticLastRetainedAdjacentFlexibleOutputCover node data m i hk
    (by omega) (by omega) (by omega) (by omega) hgen

omit hdepth hnear hsum hself in
/-- The same incomplete-stage range has actual outputs in the reverse input order. -/
theorem arithmeticLastRetainedAdjacentBeyondBoundaryReversedOutputCover
    (hlo : 2 * (i + 3) + 2 ≤ depth) (hhi : depth ≤ 3 * i + 6) :
    ∃ (C : (pullback fb fa : Scheme).OpenCover.{0})
      (out : (j : C.I₀) → C.X j ⟶ pullback q t),
      ∀ j, out j ≫ pullback.fst q t = C.f j ≫ pullback.fst fb fa ≫ fb := by
  exact arithmeticLastRetainedAdjacentFlexibleReversedOutputCover node data m i hk
    (by omega) (by omega) (by omega) (by omega) hgen

end FLT.Mazur.WeierstrassDividedDepth

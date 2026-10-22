/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedSeparatedBoundaryLocalCover
public import FLT.Mazur.WeierstrassDividedArithmeticSmoothPairSourceCover
public import FLT.Mazur.SchemeQuotientOutputCover
public import FLT.Mazur.WeierstrassDividedArithmeticFlexibleStageBounds

/-!
# Whole quotient outputs for separated near-terminal pairs

Assemble the twelve existing sources on the relative product of smooth charts.
The exact stage bound includes a feasible range beyond both boundary depths.
The full mixed last-transfer sources cover the later-zero branch.
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
  (m i j : ℕ) (hk : j + 2 ≤ n) (hgap : i + 1 < j)
  (hdepth : 2 * (j + 2) ≤ depth) (hnear : depth ≤ (i + 1) + 2 * (j + 2))
  (hstage : max (min (i + j + 2) (depth - (i + j + 2)))
    (min (i + j + 3) (depth - (i + j + 3))) ≤ j + 2)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "base" => finiteGlobalStructure hπ data (j + 2) hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m (j + 2) hk
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 2) hk m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q (j + 2) hk
local notation "a" => retainedOlderFormulaIndex (j + 2) (i + 1) (by omega)
local notation "b" => retainedOlderFormulaIndex (j + 2) (j + 1) (by omega)
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s
variable (hgen : IsLocalRing.maximalIdeal R = ideal R π)
include hgap hdepth hnear hstage hgen

/-- The twelve genuine sources cover the entire smooth separated product. -/
theorem arithmeticLastRetainedSeparatedBoundaryOutputCover :
    ∃ (C : (pullback fa fb : Scheme).OpenCover.{0})
      (out : (j : C.I₀) → C.X j ⟶ pullback q t),
      ∀ j, out j ≫ pullback.fst q t = C.f j ≫ pullback.fst fa fb ≫ fa := by
  exact arithmeticSmoothPairSource_outputCover hπ data m (j + 2) hk a b
    (arithmeticLastRetainedSeparatedBoundaryLocalSource
      node data m i j hk hgap hdepth hnear hstage)
    (arithmeticLastRetainedSeparatedBoundaryLocalInclusion
      node data m i j hk hgap hdepth hnear hstage)
    (arithmeticLastRetainedSeparatedBoundaryLocal_exists
      node data m i j hk hgap hdepth hnear hstage hgen)
    (arithmeticLastRetainedSeparatedBoundaryLocalOutput
      node data m i j hk hgap hdepth hnear hstage)
    (arithmeticLastRetainedSeparatedBoundaryLocalOutput_base
      node data m i j hk hgap hdepth hnear hstage)

/-- Exchanging the full inputs preserves coverage and the entire quotient coefficient map. -/
theorem arithmeticLastRetainedSeparatedBoundaryReversedOutputCover :
    ∃ (C : (pullback fb fa : Scheme).OpenCover.{0})
      (out : (j : C.I₀) → C.X j ⟶ pullback q t),
      ∀ j, out j ≫ pullback.fst q t = C.f j ≫ pullback.fst fb fa ≫ fb := by
  obtain ⟨C, out, h⟩ := arithmeticLastRetainedSeparatedBoundaryOutputCover
    node data m i j hk hgap hdepth hnear hstage hgen
  exact schemeQuotientOutputCover_swap (pullback.fst q t) fa fb C out h

omit hdepth hnear hstage in
/-- A nonempty range strictly beyond both previously covered exact boundary depths. -/
theorem arithmeticLastRetainedSeparatedBeyondBoundaryOutputCover
    (hlo : 2 * (j + 2) + 2 ≤ depth) (hhi : depth ≤ i + 2 * j + 4) :
    ∃ (C : (pullback fa fb : Scheme).OpenCover.{0})
      (out : (j : C.I₀) → C.X j ⟶ pullback q t),
      ∀ j, out j ≫ pullback.fst q t = C.f j ≫ pullback.fst fa fb ≫ fa := by
  exact arithmeticLastRetainedSeparatedBoundaryOutputCover node data m i j hk hgap
    (by omega) (by omega) (by omega) hgen

omit hdepth hnear hstage in
/-- The same incomplete-stage range has actual outputs in the reverse input order. -/
theorem arithmeticLastRetainedSeparatedBeyondBoundaryReversedOutputCover
    (hlo : 2 * (j + 2) + 2 ≤ depth) (hhi : depth ≤ i + 2 * j + 4) :
    ∃ (C : (pullback fb fa : Scheme).OpenCover.{0})
      (out : (j : C.I₀) → C.X j ⟶ pullback q t),
      ∀ j, out j ≫ pullback.fst q t = C.f j ≫ pullback.fst fb fa ≫ fb := by
  exact arithmeticLastRetainedSeparatedBoundaryReversedOutputCover node data m i j hk hgap
    (by omega) (by omega) (by omega) hgen

end FLT.Mazur.WeierstrassDividedDepth

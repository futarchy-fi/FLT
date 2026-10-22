/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemeQuotientOutputCover
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSelfMiddleGluing
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSelfOddCover

/-!
# Whole terminal pair covers at the two stage-one boundary depths

At depth two the middle law is already glued. At depth three the two
constructed terminal formulas cover the whole smooth terminal product.
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
local notation "f" => (O 1).ι ≫ chart 1 ≫ s

/-- The whole stage-one terminal pair has constructed local outputs at either boundary depth. -/
theorem arithmeticStageOneTerminalOutputCover (hd : depth = 2 ∨ depth = 3) :
    ∃ (C : (pullback f f : Scheme).OpenCover.{0})
      (out : (i : C.I₀) → C.X i ⟶ pullback q t),
      ∀ i, out i ≫ pullback.fst q t = C.f i ≫ pullback.fst f f ≫ f := by
  rcases hd with hd | hd
  · exact schemeQuotientOutputCover_ofWhole (pullback.fst q t) _
      (arithmeticTerminalSelfMiddleAddition hπ data m 1 hi node (by omega) hd.symm)
      (arithmeticTerminalSelfMiddleAddition_base hπ data m 1 hi node (by omega) hd.symm)
  · refine ⟨arithmeticTerminalSelfOddCover node data m 1 hi (by omega) hd,
      arithmeticTerminalSelfOddChartOutput node data m 1 hi (by omega) hd, ?_⟩
    exact arithmeticTerminalSelfOddChartOutput_base node data m 1 hi (by omega) hd

end FLT.Mazur.WeierstrassDividedDepth

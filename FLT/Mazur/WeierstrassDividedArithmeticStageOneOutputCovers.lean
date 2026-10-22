/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticStageOneInnerCovers
public import FLT.Mazur.WeierstrassDividedArithmeticStageOneTerminalCovers
public import FLT.Mazur.WeierstrassDividedArithmeticInfinityAction
public import FLT.Mazur.WeierstrassDividedArithmeticInitialAction

/-!
# All stage-one smooth arithmetic chart pairs at node depths two and three

Each of the sixteen ordered chart pairs has a genuine open cover carrying
constructed whole quotient outputs. This is coverage, without an assertion
that the normalized negative formulas agree with the original action.
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

/-- Every ordered stage-one smooth pair has a complete cover by actual quotient outputs. -/
theorem arithmeticStageOnePairOutputCover (a b : Fin 4) :
    ∃ (C : (pullback ((O a).ι ≫ chart a ≫ s)
      ((O b).ι ≫ chart b ≫ s) : Scheme).OpenCover.{0})
      (out : (i : C.I₀) → C.X i ⟶ pullback q t),
      ∀ i, out i ≫ pullback.fst q t = C.f i ≫
        pullback.fst ((O a).ι ≫ chart a ≫ s) ((O b).ι ≫ chart b ≫ s) ≫
          (O a).ι ≫ chart a ≫ s := by
  fin_cases a <;> fin_cases b
  · exact schemeQuotientOutputCover_ofWhole (pullback.fst q t) _
      (arithmeticInfinityActionQuotientOutput hπ data m 1 hi 0)
      (arithmeticInfinityActionQuotientOutput_base hπ data m 1 hi 0)
  · exact schemeQuotientOutputCover_ofWhole (pullback.fst q t) _
      (arithmeticInfinityActionQuotientOutput hπ data m 1 hi 1)
      (arithmeticInfinityActionQuotientOutput_base hπ data m 1 hi 1)
  · exact schemeQuotientOutputCover_ofWhole (pullback.fst q t) _
      (arithmeticInfinityActionQuotientOutput hπ data m 1 hi 2)
      (arithmeticInfinityActionQuotientOutput_base hπ data m 1 hi 2)
  · exact schemeQuotientOutputCover_ofWhole (pullback.fst q t) _
      (arithmeticInfinityActionQuotientOutput hπ data m 1 hi 3)
      (arithmeticInfinityActionQuotientOutput_base hπ data m 1 hi 3)
  · exact schemeQuotientOutputCover_ofWhole (pullback.fst q t) _
      (arithmeticInfinityActionReversedOutput hπ data m 1 hi 1)
      (arithmeticInfinityActionReversedOutput_base hπ data m 1 hi 1)
  · exact arithmeticStageOneTerminalOutputCover node data m hi hd
  · obtain ⟨C, out, h⟩ := arithmeticStageOneMixedOutputCover node data m hi hgen hd
    exact schemeQuotientOutputCover_swap (pullback.fst q t) _ _ C out h
  · exact schemeQuotientOutputCover_ofWhole (pullback.fst q t) _
      (arithmeticInitialActionReversedOutput hπ data m 1 hi 1)
      (arithmeticInitialActionReversedOutput_base hπ data m 1 hi 1)
  · exact schemeQuotientOutputCover_ofWhole (pullback.fst q t) _
      (arithmeticInfinityActionReversedOutput hπ data m 1 hi 2)
      (arithmeticInfinityActionReversedOutput_base hπ data m 1 hi 2)
  · exact arithmeticStageOneMixedOutputCover node data m hi hgen hd
  · exact arithmeticStageOneSelfOutputCover node data m hi hgen hd
  · exact schemeQuotientOutputCover_ofWhole (pullback.fst q t) _
      (arithmeticInitialActionReversedOutput hπ data m 1 hi 2)
      (arithmeticInitialActionReversedOutput_base hπ data m 1 hi 2)
  · exact schemeQuotientOutputCover_ofWhole (pullback.fst q t) _
      (arithmeticInfinityActionReversedOutput hπ data m 1 hi 3)
      (arithmeticInfinityActionReversedOutput_base hπ data m 1 hi 3)
  · exact schemeQuotientOutputCover_ofWhole (pullback.fst q t) _
      (arithmeticInitialActionQuotientOutput hπ data m 1 hi 1)
      (arithmeticInitialActionQuotientOutput_base hπ data m 1 hi 1)
  · exact schemeQuotientOutputCover_ofWhole (pullback.fst q t) _
      (arithmeticInitialActionQuotientOutput hπ data m 1 hi 2)
      (arithmeticInitialActionQuotientOutput_base hπ data m 1 hi 2)
  · exact schemeQuotientOutputCover_ofWhole (pullback.fst q t) _
      (arithmeticInitialActionQuotientOutput hπ data m 1 hi 3)
      (arithmeticInitialActionQuotientOutput_base hπ data m 1 hi 3)

end FLT.Mazur.WeierstrassDividedDepth

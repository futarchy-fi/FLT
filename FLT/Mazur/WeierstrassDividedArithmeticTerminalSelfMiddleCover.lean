/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSelfMiddleComparison

/-!
# Two-chart cover for exact-middle terminal self-addition

The actual tangent and reciprocal chord domains cover the entire original
arithmetic terminal self-product, and their quotient outputs are compatible.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n)
local notation "idx" => (1 : Fin (j + 3))
local notation "d" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj idx
local notation "fa" => (O).ι ≫ chart idx ≫ s
local notation "input" => arithmeticTerminalSelfReciprocalFormulaInput hπ data m j hj
local notation "al" => dividedPairLeft W (π ^ (0 + j)) (d).b3 (d).b4 (d).b6
local notation "ar" => dividedPairRight W (π ^ (0 + j)) (d).b3 (d).b4 (d).b6
local notation "V" => suppliedReciprocalChordDomain d al ar

local notation "C" => arithmeticTerminalSelfReciprocalChordOpen hπ data m j hj
local notation "T" => arithmeticTerminalSelfSmoothTangentOpen hπ data m j hj
local notation "ca" => arithmeticTerminalSelfReciprocalChordAddition hπ data m j hj
local notation "ta" => arithmeticTerminalSelfSmoothTangentAddition hπ data m j hj
local notation "cq" => arithmeticTerminalSelfReciprocalChordQuotientOutput hπ data m j hj
local notation "tq" => arithmeticTerminalSelfSmoothTangentQuotientOutput hπ data m j hj

/-- Index the two actual output domains, without changing the input product. -/
def arithmeticTerminalSelfMiddleChart : Bool → (pullback fa fa).Opens
  | false => C
  | true => T

local notation "D" => arithmeticTerminalSelfMiddleChart hπ data m j hj

/-- The quotient-valued morphism on each of the two regular charts. -/
def arithmeticTerminalSelfMiddleChartOutput : (b : Bool) → (D b).toScheme ⟶ pullback q t
  | false => cq
  | true => tq

local notation "out" => arithmeticTerminalSelfMiddleChartOutput hπ data m j hj

/-- The entire chart output preserves the original arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticTerminalSelfMiddleChartOutput_base (b : Bool) :
    out b ≫ pullback.fst q t = (D b).ι ≫ pullback.fst fa fa ≫ fa := by
  cases b
  · exact arithmeticTerminalSelfReciprocalChordQuotientOutput_base hπ data m j hj
  · exact arithmeticTerminalSelfSmoothTangentQuotientOutput_base hπ data m j hj

/-- All refinements of any pair of chart domains have the same quotient-valued output. -/
theorem arithmeticTerminalSelfMiddleChartOutput_common (b c : Bool) {X : Scheme}
    (f : X ⟶ (D b).toScheme) (g : X ⟶ (D c).toScheme)
    (h : f ≫ (D b).ι = g ≫ (D c).ι) : f ≫ out b = g ≫ out c := by
  cases b <;> cases c
  · exact congrArg (fun z => z ≫ out false) ((cancel_mono (D false).ι).mp h)
  · exact arithmeticTerminalSelfMiddle_quotient_eq hπ data m j hj f g h
  · exact (arithmeticTerminalSelfMiddle_quotient_eq hπ data m j hj g f h.symm).symm
  · exact congrArg (fun z => z ≫ out true) ((cancel_mono (D true).ι).mp h)

variable [IsLocalRing R] {depth : ℕ} (node : SplitNodeDepth W π depth)
  (hj0 : 0 < j) (hm : 2 * j = depth)

include node hj0 hm in
/-- Exact middle depth supplies coverage of every point of the full arithmetic self-product. -/
theorem arithmeticTerminalSelfMiddleChart_covers : (⨆ b, D b) = ⊤ := by
  apply top_unique
  intro p _
  rcases arithmeticTerminalSelf_middle_cover hπ data m j hj node hj0 hm p with hp | hp
  · exact (le_iSup (fun b => D b) true) hp
  · exact (le_iSup (fun b => D b) false) hp

/-- A genuine open cover retaining the complete original arithmetic terminal inputs. -/
def arithmeticTerminalSelfMiddleCover : (pullback fa fa : Scheme).OpenCover :=
  (pullback fa fa : Scheme).openCoverOfIsOpenCover D
    (arithmeticTerminalSelfMiddleChart_covers hπ data m j hj node hj0 hm)

end FLT.Mazur.WeierstrassDividedDepth

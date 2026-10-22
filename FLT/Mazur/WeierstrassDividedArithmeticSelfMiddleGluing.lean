/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticSelfMiddleComparison

/-!
# Glued middle-depth addition for full retained self-pairs

Equal retained creation depths at exact middle depth have a constructed
quotient-valued addition on their entire original smooth arithmetic product.
Both chart laws and both original coefficient morphisms are preserved.
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
  retainedSelfFormulaCoordinates retainedSelfFormulaIndex
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {nodeDepth n : ℕ}
  (node : SplitNodeDepth W π nodeDepth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (a : Option (Fin j))
local notation "hπ" => node.uniformizer_ne_zero
local notation "idx" => retainedSelfFormulaIndex j a
local notation "depth" => retainedSelfFormulaDepth j a
local notation "d" => data ⟨depth, Nat.lt_succ_of_le ((retainedSelfFormulaDepth_le j a).trans hj)⟩
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj idx
local notation "fa" => (O).ι ≫ chart idx ≫ s
local notation "coords" => tensorIntegralAtlasProjection hπ data Q j hj idx
local notation "P" => arithmeticAtlasPairPresentation hπ data m j hj idx idx
local notation "F" => retainedSelfFormulaInput hπ data j hj a
local notation "A" => DividedPairRing W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

local notation "input" => arithmeticSelfReciprocalFormulaInput hπ data m j hj a
local notation "al" => dividedPairLeft W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6
local notation "ar" => dividedPairRight W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

local notation "V" => suppliedReciprocalChordDomain d al ar

local notation "C" => arithmeticSelfReciprocalChordOpen node data m j hj a
local notation "T" => arithmeticSelfSmoothTangentOpen node data m j hj a
local notation "ca" => arithmeticSelfReciprocalChordAddition node data m j hj a
local notation "ta" => arithmeticSelfSmoothTangentAddition node data m j hj a
local notation "cq" => arithmeticSelfReciprocalChordQuotientOutput node data m j hj a

local notation "tq" => arithmeticSelfSmoothTangentQuotientOutput node data m j hj a

/-- Index the two actual output domains, without changing the input product. -/
def arithmeticSelfMiddleChart : Bool → (pullback fa fa).Opens
  | false => C
  | true => T

local notation "D" => arithmeticSelfMiddleChart node data m j hj a

/-- The quotient-valued morphism on each of the two regular charts. -/
def arithmeticSelfMiddleChartOutput : (b : Bool) → (D b).toScheme ⟶ pullback q t
  | false => cq
  | true => tq

local notation "out" => arithmeticSelfMiddleChartOutput node data m j hj a

/-- The entire chart output preserves the original arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticSelfMiddleChartOutput_base (b : Bool) :
    out b ≫ pullback.fst q t = (D b).ι ≫ pullback.fst fa fa ≫ fa := by
  cases b
  · exact arithmeticSelfReciprocalChordQuotientOutput_base node data m j hj a
  · exact arithmeticSelfSmoothTangentQuotientOutput_base node data m j hj a

/-- All refinements of any pair of chart domains have the same quotient-valued output. -/
theorem arithmeticSelfMiddleChartOutput_common (b c : Bool) {X : Scheme}
    (f : X ⟶ (D b).toScheme) (g : X ⟶ (D c).toScheme)
    (h : f ≫ (D b).ι = g ≫ (D c).ι) : f ≫ out b = g ≫ out c := by
  cases b <;> cases c
  · exact congrArg (fun z => z ≫ out false) ((cancel_mono (D false).ι).mp h)
  · exact arithmeticSelfMiddle_quotient_eq node data m j hj a f g h
  · exact (arithmeticSelfMiddle_quotient_eq node data m j hj a g f h.symm).symm
  · exact congrArg (fun z => z ≫ out true) ((cancel_mono (D true).ι).mp h)

variable (hd0 : 0 < retainedSelfFormulaDepth j a)
  (hm : 2 * retainedSelfFormulaDepth j a = nodeDepth)

include hd0 hm in
/-- Exact middle depth supplies coverage of every point of the full arithmetic self-product. -/
theorem arithmeticSelfMiddleChart_covers : (⨆ b, D b) = ⊤ := by
  apply top_unique
  intro p _
  rcases arithmeticSelf_middle_cover node data m j hj a hd0 hm p with hp | hp
  · exact (le_iSup (fun b => D b) true) hp
  · exact (le_iSup (fun b => D b) false) hp

/-- A genuine open cover retaining the complete original arithmetic retained inputs. -/
def arithmeticSelfMiddleCover : (pullback fa fa : Scheme).OpenCover :=
  (pullback fa fa : Scheme).openCoverOfIsOpenCover D
    (arithmeticSelfMiddleChart_covers node data m j hj a hd0 hm)


local notation "cover" => arithmeticSelfMiddleCover node data m j hj a hd0 hm

/-- Glue the constructed laws on the full arithmetic retained self-product. -/
def arithmeticSelfMiddleAddition : pullback fa fa ⟶ pullback q t :=
  (cover).glueMorphisms out (fun b c =>
    arithmeticSelfMiddleChartOutput_common node data m j hj a b c _ _ pullback.condition)

local notation "add" => arithmeticSelfMiddleAddition node data m j hj a hd0 hm

/-- Every actual chart formula is retained by the glued quotient-valued output. -/
@[reassoc] theorem arithmeticSelfMiddleAddition_chart (b : Bool) :
    (D b).ι ≫ add = out b :=
  (cover).ι_glueMorphisms _ _ b

/-- The full reciprocal chord output is a restriction of the glued morphism. -/
@[reassoc] theorem arithmeticSelfMiddleAddition_reciprocalChord :
    (C).ι ≫ add = cq :=
  arithmeticSelfMiddleAddition_chart node data m j hj a hd0 hm false

/-- The full tangent output is a restriction of the same glued morphism. -/
@[reassoc] theorem arithmeticSelfMiddleAddition_tangent : (T).ι ≫ add = tq :=
  arithmeticSelfMiddleAddition_chart node data m j hj a hd0 hm true

/-- Gluing preserves the original first arithmetic coefficient morphism, including nilpotents. -/
@[reassoc] theorem arithmeticSelfMiddleAddition_base :
    add ≫ pullback.fst q t = pullback.fst fa fa ≫ fa := by
  apply (cover).hom_ext
  intro b
  change (D b).ι ≫ _ = (D b).ι ≫ _
  rw [arithmeticSelfMiddleAddition_chart_assoc,
    arithmeticSelfMiddleChartOutput_base]

/-- The output also preserves the second original arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticSelfMiddleAddition_base_snd :
    add ≫ pullback.fst q t = pullback.snd fa fa ≫ fa := by
  rw [arithmeticSelfMiddleAddition_base, pullback.condition]

/-- The two actual formulas uniquely determine the entire glued quotient output. -/
theorem arithmeticSelfMiddleAddition_unique
    (f : pullback fa fa ⟶ pullback q t)
    (hc : (C).ι ≫ f = cq) (ht : (T).ι ≫ f = tq) : f = add := by
  apply (cover).hom_ext
  intro b
  change (D b).ι ≫ f = (D b).ι ≫ add
  rw [arithmeticSelfMiddleAddition_chart]
  cases b
  · exact hc
  · exact ht

end FLT.Mazur.WeierstrassDividedDepth

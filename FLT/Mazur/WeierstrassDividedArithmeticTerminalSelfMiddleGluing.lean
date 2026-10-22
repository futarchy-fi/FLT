/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSelfMiddleCover

/-!
# Glued exact-middle arithmetic terminal addition

Construct a single quotient-valued morphism on the complete terminal
self-product. Both chart formulas, the whole coefficient morphisms and
uniqueness are retained; no residue-field replacement is involved.
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

variable [IsLocalRing R] {depth : ℕ} (node : SplitNodeDepth W π depth)
  (hj0 : 0 < j) (hm : 2 * j = depth)
local notation "cover" => arithmeticTerminalSelfMiddleCover hπ data m j hj node hj0 hm
local notation "D" => arithmeticTerminalSelfMiddleChart hπ data m j hj
local notation "out" => arithmeticTerminalSelfMiddleChartOutput hπ data m j hj

/-- Glue the constructed laws on the full arithmetic terminal self-product. -/
def arithmeticTerminalSelfMiddleAddition : pullback fa fa ⟶ pullback q t :=
  (cover).glueMorphisms out (fun b c =>
    arithmeticTerminalSelfMiddleChartOutput_common hπ data m j hj b c _ _ pullback.condition)

local notation "add" => arithmeticTerminalSelfMiddleAddition hπ data m j hj node hj0 hm

/-- Every actual chart formula is retained by the glued quotient-valued output. -/
@[reassoc] theorem arithmeticTerminalSelfMiddleAddition_chart (b : Bool) :
    (D b).ι ≫ add = out b :=
  (cover).ι_glueMorphisms _ _ b

/-- The full reciprocal chord output is a restriction of the glued morphism. -/
@[reassoc] theorem arithmeticTerminalSelfMiddleAddition_reciprocalChord :
    (C).ι ≫ add = cq :=
  arithmeticTerminalSelfMiddleAddition_chart hπ data m j hj node hj0 hm false

/-- The full tangent output is a restriction of the same glued morphism. -/
@[reassoc] theorem arithmeticTerminalSelfMiddleAddition_tangent : (T).ι ≫ add = tq :=
  arithmeticTerminalSelfMiddleAddition_chart hπ data m j hj node hj0 hm true

/-- Gluing preserves the original first arithmetic coefficient morphism, including nilpotents. -/
@[reassoc] theorem arithmeticTerminalSelfMiddleAddition_base :
    add ≫ pullback.fst q t = pullback.fst fa fa ≫ fa := by
  apply (cover).hom_ext
  intro b
  change (D b).ι ≫ _ = (D b).ι ≫ _
  rw [arithmeticTerminalSelfMiddleAddition_chart_assoc,
    arithmeticTerminalSelfMiddleChartOutput_base]

/-- The output also preserves the second original arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticTerminalSelfMiddleAddition_base_snd :
    add ≫ pullback.fst q t = pullback.snd fa fa ≫ fa := by
  rw [arithmeticTerminalSelfMiddleAddition_base, pullback.condition]

/-- The two actual formulas uniquely determine the entire glued quotient output. -/
theorem arithmeticTerminalSelfMiddleAddition_unique
    (f : pullback fa fa ⟶ pullback q t)
    (hc : (C).ι ≫ f = cq) (ht : (T).ι ≫ f = tq) : f = add := by
  apply (cover).hom_ext
  intro b
  change (D b).ι ≫ f = (D b).ι ≫ add
  rw [arithmeticTerminalSelfMiddleAddition_chart]
  cases b
  · exact hc
  · exact ht

end FLT.Mazur.WeierstrassDividedDepth

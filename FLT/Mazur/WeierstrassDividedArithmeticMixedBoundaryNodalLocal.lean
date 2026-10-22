/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentMixedNodalCover
public import FLT.Mazur.WeierstrassDividedArithmeticSmoothPairInclusion

/-!
# Local sources for the full retained/terminal boundary pair

Combine unshifted normalized formulas and the genuine adjacent incidence
sources. Every source embeds openly in the unchanged full arithmetic pair
and has a constructed quotient output with its full coefficient identity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  arithmeticRetainedTensorIso olderSuccessiveTensorAtlasIso finiteTensorAtlasObject
  arithmeticFixedAdjacentPairOpen arithmeticFixedAdjacentPairTransfer
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (k : ℕ) (hk : k + 2 ≤ j)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "a" => (Fin.succ ⟨j - k, by omega⟩ : Fin (j + 3))
local notation "b" => (Fin.succ ⟨j - (k + 1), by omega⟩ : Fin (j + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O 1).ι ≫ chart 1 ≫ s
local notation "f" => chart a ≫ s
local notation "f'" => chart b ≫ s
local notation "g" => chart 1 ≫ s
local notation "B" => arithmeticFixedAdjacentPairOpen hπ data m j hj k hk g
local notation "transfer" => arithmeticFixedAdjacentPairTransfer hπ data m j hj k hk g
local notation "x" => (B).ι ≫ pullback.fst f g
local notation "y" => (B).ι ≫ pullback.snd f g
local notation "z" => transfer ≫ pullback.fst f' g
local notation "w" => transfer ≫ pullback.snd f' g
local notation "D" => arithmeticAdjacentMixedNodalSmoothOpen node data m j hj k hk
variable (hdepth : 2 * j ≤ depth) (hnear : depth ≤ k + 2 * j)
local notation "E" => arithmeticMixedNodalReflectedChart
  node data m j hj k (by omega) hdepth hnear
local notation "C" => arithmeticAdjacentMixedNodalChart
  node data m j hj k hk hdepth (by omega)
local notation "inc" => arithmeticSmoothPairInclusion hπ data m j hj a 1

/-- Three normalized formulas before or after the retained input transfers. -/
abbrev MixedBoundaryNodalLocalIndex := Bool × Fin 3

/-- Each source is an actual open in its original smooth pair or incidence domain. -/
def arithmeticMixedBoundaryNodalLocalSource : MixedBoundaryNodalLocalIndex → Scheme
  | (false, c) => (E c).toScheme
  | (true, c) => (C c).toScheme

local notation "X" => arithmeticMixedBoundaryNodalLocalSource node data m j hj k hk hdepth hnear

/-- Include the six formula sources into the full original retained/terminal pair. -/
def arithmeticMixedBoundaryNodalLocalInclusion :
    (c : MixedBoundaryNodalLocalIndex) → X c ⟶ pullback f g
  | (false, c) => (E c).ι ≫ inc
  | (true, c) => (C c).ι ≫ (D).ι ≫ (B).ι

local notation "J" => arithmeticMixedBoundaryNodalLocalInclusion
  node data m j hj k hk hdepth hnear

/-- All sources are genuine open subcharts of the unchanged original pair. -/
instance arithmeticMixedBoundaryNodalLocalInclusion_open (c : MixedBoundaryNodalLocalIndex) :
    IsOpenImmersion (J c) := by
  rcases c with ⟨flag, c⟩
  cases flag <;> dsimp only [arithmeticMixedBoundaryNodalLocalInclusion] <;> infer_instance

/-- Both transfer choices carry whole normalized quotient-valued outputs. -/
def arithmeticMixedBoundaryNodalLocalOutput :
    (c : MixedBoundaryNodalLocalIndex) → X c ⟶ pullback q t
  | (false, c) => arithmeticMixedNodalReflectedQuotientOutput
      node data m j hj k (by omega) hdepth hnear c
  | (true, c) => arithmeticAdjacentMixedNodalOutput
      node data m j hj k hk hdepth (by omega) c

/-- The entire original coefficient morphism survives both choices. -/
@[reassoc] theorem arithmeticMixedBoundaryNodalLocalOutput_base
    (c : MixedBoundaryNodalLocalIndex) :
    arithmeticMixedBoundaryNodalLocalOutput node data m j hj k hk hdepth hnear c ≫
      pullback.fst q t = J c ≫ pullback.fst f g ≫ f := by
  rcases c with ⟨flag, c⟩
  cases flag <;>
    simp only [arithmeticMixedBoundaryNodalLocalOutput,
      arithmeticMixedBoundaryNodalLocalInclusion, Category.assoc,
      arithmeticMixedNodalReflectedQuotientOutput_base,
      arithmeticAdjacentMixedNodalOutput_base, arithmeticSmoothPairInclusion_first_assoc,
      retainedOlderFormulaIndex]
  rfl

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentMixedNodalCover
public import FLT.Mazur.WeierstrassDividedArithmeticSmoothPairInclusion
public import FLT.Mazur.WeierstrassDividedArithmeticMixedDifferenceQuotientOutput

/-!
# Actual sources for creation-zero mixed boundary pairs

The unshifted difference formula and three adjacent-transfer formulas have
actual source inclusions and full quotient-valued outputs. The positive
transferred depth permits normalized coverage at the odd endpoint.
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
local notation "a" => (Fin.succ ⟨j - k,
  Nat.lt_succ_of_le ((Nat.sub_le j k).trans (Nat.le_succ j))⟩ : Fin (j + 3))
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
local notation "D" => arithmeticAdjacentMixedNodalSmoothOpen node data m j hj k hk
variable (hdepth : 2 * j ≤ depth) (hnear : depth ≤ (k + 1) + 2 * j)
local notation "E" => arithmeticRetainedTerminalOpen
  hπ data m j hj k j (by omega) le_rfl (by omega)
local notation "C" => arithmeticAdjacentMixedNodalChart
  node data m j hj k hk hdepth (by omega)
local notation "inc" => arithmeticSmoothPairInclusion hπ data m j hj a 1

/-- The unshifted difference formula and three normalized transfer formulas. -/
abbrev MixedZeroBoundaryNodalLocalIndex := Option (Fin 3)

/-- Each source is an actual open in its original smooth pair or incidence domain. -/
def arithmeticMixedZeroBoundaryNodalLocalSource : MixedZeroBoundaryNodalLocalIndex → Scheme
  | none => (E).toScheme
  | some c => (C c).toScheme

local notation "X" => arithmeticMixedZeroBoundaryNodalLocalSource node data m j hj k hk hdepth hnear

/-- Include the four formula sources into the full original retained/terminal pair. -/
def arithmeticMixedZeroBoundaryNodalLocalInclusion :
    (c : MixedZeroBoundaryNodalLocalIndex) → X c ⟶ pullback f g
  | none => (E).ι ≫ inc
  | some c => (C c).ι ≫ (D).ι ≫ (B).ι

local notation "J" => arithmeticMixedZeroBoundaryNodalLocalInclusion
  node data m j hj k hk hdepth hnear

/-- All sources are genuine open subcharts of the unchanged original pair. -/
instance arithmeticMixedZeroBoundaryNodalLocalInclusion_open
    (c : MixedZeroBoundaryNodalLocalIndex) :
    IsOpenImmersion (J c) := by
  cases c <;> dsimp only [arithmeticMixedZeroBoundaryNodalLocalInclusion] <;> infer_instance

/-- Both transfer choices carry whole normalized quotient-valued outputs. -/
def arithmeticMixedZeroBoundaryNodalLocalOutput :
    (c : MixedZeroBoundaryNodalLocalIndex) → X c ⟶ pullback q t
  | none => arithmeticMixedDifferenceQuotientOutput node data m j hj k (by omega)
  | some c => arithmeticAdjacentMixedNodalOutput
      node data m j hj k hk hdepth (by omega) c

/-- The entire original coefficient morphism survives both choices. -/
@[reassoc] theorem arithmeticMixedZeroBoundaryNodalLocalOutput_base
    (c : MixedZeroBoundaryNodalLocalIndex) :
    arithmeticMixedZeroBoundaryNodalLocalOutput node data m j hj k hk hdepth hnear c ≫
      pullback.fst q t = J c ≫ pullback.fst f g ≫ f := by
  cases c <;>
    simp only [arithmeticMixedZeroBoundaryNodalLocalOutput,
      arithmeticMixedZeroBoundaryNodalLocalInclusion, Category.assoc,
      arithmeticMixedDifferenceQuotientOutput_base,
      arithmeticAdjacentMixedNodalOutput_base, arithmeticSmoothPairInclusion_first_assoc,
      retainedOlderFormulaIndex]
  rfl

end FLT.Mazur.WeierstrassDividedDepth

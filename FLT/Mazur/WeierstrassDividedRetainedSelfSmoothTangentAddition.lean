/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedSelfReciprocalAddition
public import FLT.Mazur.WeierstrassDividedAtlasPairSmoothTangentAddition

/-!
# Smooth tangent addition on retained self-pairs

Keep the full original initial or retained chart in both factors. Punctured
zero-depth inputs with nonzero tangent denominator supply the actual smooth output domain.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (j : ℕ) (hj : j ≤ n) (a : Option (Fin j))

local notation "idx" => retainedSelfFormulaIndex j a
local notation "depth" => retainedSelfFormulaDepth j a
local notation "d" => data ⟨depth, Nat.lt_succ_of_le ((retainedSelfFormulaDepth_le j a).trans hj)⟩

local notation "f" => retainedSelfFormulaCoordinates hπ data j hj a

local notation "hf" => retainedSelfFormulaCoordinates_structure hπ data j hj a
variable [IsNoetherianRing R]
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "ta" => globalSmoothAtlasMap hπ data j hj idx ≫ t
local notation "P" => DividedPairRing W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

local notation "input" => retainedSelfFormulaInput hπ data j hj a
local notation "al" => dividedPairLeft W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6
local notation "ar" => dividedPairRight W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

/-- The smooth tangent domain of the actual full equal-creation-depth pair. -/
def retainedSelfSmoothTangentOpen : (pullback ta ta).Opens :=
  atlasPairSmoothTangentOpen hπ data j hj idx idx d f f hf hf

local notation "V" => retainedSelfSmoothTangentOpen hπ data j hj a

/-- Construct the smooth tangent output in the unchanged final smooth model. -/
def retainedSelfSmoothTangentAddition : (V).toScheme ⟶ (U).toScheme :=
  atlasPairSmoothTangentAddition hπ data j hj idx idx d f f hf hf

local notation "add" => retainedSelfSmoothTangentAddition hπ data j hj a

/-- The output keeps the first original input's coefficient point. -/
@[reassoc] theorem retainedSelfSmoothTangentAddition_structure :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj idx idx ≫
      pullback.fst t t ≫ t :=
  atlasPairSmoothTangentAddition_structure hπ data j hj idx idx d f f hf hf

/-- The output keeps the second original input's coefficient point as well. -/
@[reassoc] theorem retainedSelfSmoothTangentAddition_structure_snd :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj idx idx ≫
      pullback.snd t t ≫ t := by
  rw [retainedSelfSmoothTangentAddition_structure, pullback.condition]

/-- Its original cubic contraction is precisely the constructed smooth tangent formula. -/
@[reassoc] theorem retainedSelfSmoothTangentAddition_contraction :
    add ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (input ∣_ suppliedSmoothTangentDomain d al ar) ≫ suppliedSmoothTangentOriginalSmooth d al ar ≫
        (WeierstrassIntegralChart.integralSmoothOpen W).ι :=
  atlasPairSmoothTangentAddition_contraction hπ data j hj idx idx d f f hf hf

local notation "x₁" => al (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "y₁" => al (y W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "x₂" => ar (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "y₂" => ar (y W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "α" => algebraMap R P W.a₁

variable [IsLocalRing R] {nodeDepth : ℕ} (node : SplitNodeDepth W π nodeDepth)

include node

/-- Initial and zero-created self-pairs with nonzero tangent denominator are covered. -/
theorem retainedSelfSmoothTangentOpen_zero_mem (hz : depth = 0) (hm : 0 < nodeDepth)
    (p : (pullback ta ta : Scheme))
    (hp : algebraMap R P π ∈ (input p).asIdeal)
    (hx : x₁ ∉ (input p).asIdeal) (hu : x₂ ∉ (input p).asIdeal)
    (hd : dividedTangentDenominator W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6 al ar ∉
      (input p).asIdeal) : p ∈ V :=
  atlasPairSmoothTangentOpen_zero_mem hπ data j hj idx idx d f f hf hf node
    (by change 0 + depth = 0; omega) hm p hp hx hu hd

end FLT.Mazur.WeierstrassDividedDepth

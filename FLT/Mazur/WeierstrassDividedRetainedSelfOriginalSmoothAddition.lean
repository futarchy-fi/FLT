/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedSelfReciprocalAddition
public import FLT.Mazur.WeierstrassDividedAtlasPairOriginalSmoothAddition

/-!
# Smooth secant addition on retained self-pairs

Keep the full original initial or retained chart in both factors. All
punctured zero-depth inputs supply the actual smooth output domain.
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

/-- The original smooth domain of the actual full equal-creation-depth pair. -/
def retainedSelfOriginalSmoothOpen : (pullback ta ta).Opens :=
  atlasPairOriginalSmoothOpen hπ data j hj idx idx d f f hf hf

local notation "V" => retainedSelfOriginalSmoothOpen hπ data j hj a

/-- Construct the original smooth output in the unchanged final smooth model. -/
def retainedSelfOriginalSmoothAddition : (V).toScheme ⟶ (U).toScheme :=
  atlasPairOriginalSmoothAddition hπ data j hj idx idx d f f hf hf

local notation "add" => retainedSelfOriginalSmoothAddition hπ data j hj a

/-- The output keeps the first original input's coefficient point. -/
@[reassoc] theorem retainedSelfOriginalSmoothAddition_structure :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj idx idx ≫
      pullback.fst t t ≫ t :=
  atlasPairOriginalSmoothAddition_structure hπ data j hj idx idx d f f hf hf

/-- The output keeps the second original input's coefficient point as well. -/
@[reassoc] theorem retainedSelfOriginalSmoothAddition_structure_snd :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj idx idx ≫
      pullback.snd t t ≫ t := by
  rw [retainedSelfOriginalSmoothAddition_structure, pullback.condition]

/-- Its original cubic contraction is precisely the constructed original smooth formula. -/
@[reassoc] theorem retainedSelfOriginalSmoothAddition_contraction :
    add ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (input ∣_ suppliedOriginalSmoothDomain d al ar) ≫ suppliedOriginalSmoothAddition d al ar ≫
        (WeierstrassIntegralChart.integralSmoothOpen W).ι :=
  atlasPairOriginalSmoothAddition_contraction hπ data j hj idx idx d f f hf hf

local notation "x₁" => al (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "y₁" => al (y W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "x₂" => ar (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "y₂" => ar (y W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "α" => algebraMap R P W.a₁

variable [IsLocalRing R] {nodeDepth : ℕ} (node : SplitNodeDepth W π nodeDepth)

include node

/-- All punctured initial and zero-created self-pairs are covered, including equal points. -/
theorem retainedSelfOriginalSmoothOpen_zero_mem (hz : depth = 0) (hm : 0 < nodeDepth)
    (p : (pullback ta ta : Scheme))
    (hp : algebraMap R P π ∈ (input p).asIdeal)
    (hx : x₁ ∉ (input p).asIdeal) (hu : x₂ ∉ (input p).asIdeal) : p ∈ V :=
  atlasPairOriginalSmoothOpen_zero_mem hπ data j hj idx idx d f f hf hf node
    (by change 0 + depth = 0; omega) hm p hp hx hu

end FLT.Mazur.WeierstrassDividedDepth

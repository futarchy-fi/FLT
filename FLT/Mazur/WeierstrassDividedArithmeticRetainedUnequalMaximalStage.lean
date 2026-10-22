/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedSeparatedFlexibleReversed
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedAdjacentFlexibleReversed
public import FLT.Mazur.WeierstrassDividedDepthFeasibility

/-!
# Unequal retained smooth-pair covers at the actual maximal stage

At a stage within one of half the node depth, all three output-stage bounds
hold automatically. Actual division data provide the remaining strict depth
bounds. This covers positive separated and adjacent retained pairs in either
input order, assuming only that their one-step transfers exist in the stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure

/-- Every sum or its reflection fits in the actual maximal resolved stage. -/
theorem retainedMaximalStage_min {d k : ℕ} (h : d ≤ 2 * k + 1) (r : ℕ) :
    min r (d - r) ≤ k := by omega

/-- All three possible sums after zero, one or two transfers fit simultaneously. -/
theorem retainedMaximalStage_three {d k : ℕ} (h : d ≤ 2 * k + 1) (r : ℕ) :
    max (min r (d - r))
      (max (min (r + 1) (d - (r + 1))) (min (r + 2) (d - (r + 2)))) ≤ k :=
  max_le (retainedMaximalStage_min h r)
    (max_le (retainedMaximalStage_min h (r + 1)) (retainedMaximalStage_min h (r + 2)))

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m k : ℕ) (hk : k ≤ n) (hmax : depth ≤ 2 * k + 1)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

omit [IsDomain R] [IsBezout R] [IsNoetherianRing R] in
include node data hk in
/-- The supplied transfer stage forces both shifted inputs strictly before the middle. -/
theorem retainedMaximalStage_pre (j : ℕ) (hj : j + 3 ≤ k) : 2 * (j + 2) < depth := by
  have hd := dataFamily_twice_stage_le node data k hk
  omega

section Separated
variable (i j : ℕ) (hgap : i + 1 < j) (hj : j + 3 ≤ k)
local notation "pre" => retainedMaximalStage_pre node data k hk j hj
local notation "stage" => retainedMaximalStage_three hmax (i + j + 2)
local notation "A" => arithmeticRetainedSeparatedFlexiblePreMiddleSmoothOpen node data m k hk i j
local notation "B" => arithmeticRetainedSeparatedFlexibleReversedSmoothOpen node data m k hk i j

/-- The forward smooth-pair cover needs no independent node-depth or output-stage premise. -/
def arithmeticRetainedSeparatedMaximalStageCover : (A).toScheme.OpenCover :=
  arithmeticRetainedSeparatedFlexiblePreMiddleSmoothCover
    node data m k hk i j (by omega) (by omega) (by omega) (by omega) hgap pre stage
      node.maximalIdeal_eq

/-- Every forward cover member retains the entire constructed quotient output. -/
def arithmeticRetainedSeparatedMaximalStageOutput
    (b : RetainedSeparatedFlexiblePreMiddleLocalIndex) :
    (arithmeticRetainedSeparatedMaximalStageCover
      node data m k hk hmax i j hgap hj).X b ⟶ pullback q t :=
  arithmeticRetainedSeparatedFlexiblePreMiddleSmoothOutput
    node data m k hk i j (by omega) (by omega) (by omega) (by omega) hgap pre stage b

/-- The reversed smooth-pair cover has the same automatic depth and stage bounds. -/
def arithmeticRetainedSeparatedMaximalStageReversedCover : (B).toScheme.OpenCover :=
  arithmeticRetainedSeparatedFlexibleReversedSmoothCover
    node data m k hk i j (by omega) (by omega) (by omega) (by omega) hgap pre stage
      node.maximalIdeal_eq

/-- Every reversed member retains its complete quotient-valued output. -/
def arithmeticRetainedSeparatedMaximalStageReversedOutput
    (b : RetainedSeparatedFlexiblePreMiddleLocalIndex) :
    (arithmeticRetainedSeparatedMaximalStageReversedCover
      node data m k hk hmax i j hgap hj).X b ⟶ pullback q t :=
  arithmeticRetainedSeparatedFlexibleReversedSmoothOutput
    node data m k hk i j (by omega) (by omega) (by omega) (by omega) hgap pre stage b

end Separated

section Adjacent
variable (i : ℕ) (hi : i + 4 ≤ k)
local notation "pre" => retainedMaximalStage_pre node data k hk (i + 1) hi
local notation "stage" => retainedMaximalStage_three hmax (2 * i + 3)
local notation "A" => arithmeticRetainedAdjacentFlexiblePreMiddleSmoothOpen node data m k hk i
local notation "B" => arithmeticRetainedAdjacentFlexibleReversedSmoothOpen node data m k hk i

/-- The forward smooth-pair cover needs no independent node-depth or output-stage premise. -/
def arithmeticRetainedAdjacentMaximalStageCover : (A).toScheme.OpenCover :=
  arithmeticRetainedAdjacentFlexiblePreMiddleSmoothCover
    node data m k hk i (by omega) (by omega) (by omega) pre stage node.maximalIdeal_eq

/-- Every forward cover member retains the entire constructed quotient output. -/
def arithmeticRetainedAdjacentMaximalStageOutput (b : RetainedAdjacentFlexiblePreMiddleLocalIndex) :
    (arithmeticRetainedAdjacentMaximalStageCover node data m k hk hmax i hi).X b ⟶ pullback q t :=
  arithmeticRetainedAdjacentFlexiblePreMiddleSmoothOutput
    node data m k hk i (by omega) (by omega) (by omega) pre stage b

/-- The reversed smooth-pair cover has the same automatic depth and stage bounds. -/
def arithmeticRetainedAdjacentMaximalStageReversedCover : (B).toScheme.OpenCover :=
  arithmeticRetainedAdjacentFlexibleReversedSmoothCover
    node data m k hk i (by omega) (by omega) (by omega) pre stage node.maximalIdeal_eq

/-- Every reversed member retains its complete quotient-valued output. -/
def arithmeticRetainedAdjacentMaximalStageReversedOutput
    (b : RetainedAdjacentFlexiblePreMiddleLocalIndex) :
    (arithmeticRetainedAdjacentMaximalStageReversedCover
      node data m k hk hmax i hi).X b ⟶ pullback q t :=
  arithmeticRetainedAdjacentFlexibleReversedSmoothOutput
    node data m k hk i (by omega) (by omega) (by omega) pre stage b

end Adjacent

end FLT.Mazur.WeierstrassDividedDepth

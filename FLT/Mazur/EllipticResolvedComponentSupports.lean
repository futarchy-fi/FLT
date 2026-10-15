/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedComponentAtlasCoverage
public import FLT.Mazur.EllipticResolvedRetainedIdentitySeparation
public import FLT.Mazur.EllipticResolvedRetainedTerminalSeparation
public import FLT.Mazur.WeierstrassDividedTensorResidueInfinity

/-!
# Supports of the actual arithmetic component charts

Record the original-fiber images before restricting to the smooth locus.
The retained and terminal supports are the full boundaries already separated
by the incidence equations, independently of arithmetic point lifting.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (r : (ResidueField A)ˣ)
local notation "F" => ResidueField A
local notation "p" => resolvedSplitStructure A D
local notation "g" => globalDividedTensorChart (SplitNodeDepth.uniformizer_ne_zero D)
  (splitResolutionData A D) F (depth / 2) (le_refl _)

/-- The original-fiber image of each arithmetic torus before smooth restriction. -/
def resolvedComponentCarrier (i : ResolvedComponentIndex depth) : Set (resolvedSplitFiber A D) :=
  match i with
  | .identity => Set.range (resolvedIdentityChart A D)
  | .retainedPositive j hj0 hj => Set.range (resolvedRetainedPositiveChart A D r j hj0 hj)
  | .retainedNegative j hj0 hj => Set.range (resolvedRetainedNegativeChart A D r j hj0 hj)
  | .terminalPositive hk0 hp => Set.range (resolvedTerminalPositiveChart A D r hk0 hp)
  | .terminalNegative hk0 hp => Set.range (resolvedTerminalNegativeChart A D r hk0 hp)
  | .terminalMiddle hk0 hm => Set.range (resolvedTerminalMiddleChart A D r hk0 hm)

/-- Including any smooth component chart recovers its original-fiber image. -/
theorem resolvedComponentChart_range_inclusion (i : ResolvedComponentIndex depth) :
    Set.range (resolvedComponentChart A D r i ≫ (p).smoothLocus.ι) =
      resolvedComponentCarrier A D r i := by
  cases i <;> simp only [resolvedComponentChart, resolvedComponentCarrier,
    resolvedIdentitySmoothChart_inclusion, resolvedRetainedPositiveSmoothChart_inclusion,
    resolvedRetainedNegativeSmoothChart_inclusion, resolvedTerminalPositiveSmoothChart_inclusion,
    resolvedTerminalNegativeSmoothChart_inclusion, resolvedTerminalMiddleSmoothChart_inclusion]

/-- The positive retained torus lies in its full arithmetic boundary. -/
theorem resolvedRetainedPositiveChart_subset_boundary (j : ℕ)
    (hj0 : 0 < j) (hj : j < depth / 2) :
    Set.range (resolvedRetainedPositiveChart A D r j hj0 hj) ⊆
      Set.range (resolvedRetainedBoundaryChart A D j hj) := by
  rw [← resolvedRetainedCharts_cover A D r j hj0 hj]
  exact Set.subset_union_right

/-- The negative retained torus lies in its full arithmetic boundary. -/
theorem resolvedRetainedNegativeChart_subset_boundary (j : ℕ)
    (hj0 : 0 < j) (hj : j < depth / 2) :
    Set.range (resolvedRetainedNegativeChart A D r j hj0 hj) ⊆
      Set.range (resolvedRetainedBoundaryChart A D j hj) := by
  rw [← resolvedRetainedCharts_cover A D r j hj0 hj]
  exact Set.subset_union_left

/-- The positive terminal torus lies in the full final tensor chart. -/
theorem resolvedTerminalPositiveChart_subset_terminal
    (hk0 : 0 < depth / 2) (hp : 2 * (depth / 2) < depth) :
    Set.range (resolvedTerminalPositiveChart A D r hk0 hp) ⊆ Set.range g := by
  have h := resolvedTerminalCharts_cover A D r hk0 hp
  exact (Set.subset_union_right.trans (Set.Subset.rfl.trans_eq h)).trans
    Set.inter_subset_left

/-- The negative terminal torus lies in the full final tensor chart. -/
theorem resolvedTerminalNegativeChart_subset_terminal
    (hk0 : 0 < depth / 2) (hp : 2 * (depth / 2) < depth) :
    Set.range (resolvedTerminalNegativeChart A D r hk0 hp) ⊆ Set.range g := by
  have h := resolvedTerminalCharts_cover A D r hk0 hp
  exact (Set.subset_union_left.trans (Set.Subset.rfl.trans_eq h)).trans
    Set.inter_subset_left

end FLT.Mazur.WeierstrassDividedDepth

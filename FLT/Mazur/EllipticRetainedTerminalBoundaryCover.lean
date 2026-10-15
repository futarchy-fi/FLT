/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticRetainedSmoothBoundaryCover
public import FLT.Mazur.WeierstrassDividedGlobalConicCoordinates
public import FLT.Mazur.WeierstrassDividedTerminalParameterOrigins

/-!
# The last positive-depth exterior meets the original terminal chart

The entire conic boundary factors through the actual divided chart. Thus
every smooth point of the last exterior is in its retained arithmetic
boundary or the terminal atlas member, for either terminal parity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
local notation "F" => ResidueField A
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "φ" => WeierstrassSuccessiveX.residueDividedConicMap D (start + j) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A F))
local notation "p" => pullback.fst q (finiteGlobalStructure hπ data (j + 1) hj)
local notation "g" => globalSuccessiveTensorChart hπ data F j hj
local notation "terminal" => globalDividedTensorChart hπ data F (j + 1) hj
local notation "c" => olderGlobalConicBoundary hπ data D j hj 0 hj hk0 hk
local notation "b" => finiteRetainedBoundaryTensorChart A hπ data j hj 0 hj F

/-- The whole last conic boundary lies in the original divided atlas member. -/
theorem lastConicBoundary_range_subset_terminal : Set.range c ⊆ Set.range terminal := by
  have he := globalDividedConicCoordinates_chart hπ data D j hj hk0 hk
  have hc : Spec.map (CommRingCat.ofHom (φ).toRingHom) ≫ terminal = c := by
    unfold olderGlobalConicBoundary olderGlobalMiddleConic
    rw [olderGlobalTensorChart_zero_retention]
    exact he
  rintro z ⟨x, rfl⟩
  exact ⟨Spec.map (CommRingCat.ofHom (φ).toRingHom) x, congrArg (fun m => m x) hc⟩

include D hk0 hk in
/-- Every smooth point in the last positive-depth exterior is already on one of these opens. -/
theorem lastRetainedExterior_smooth_cover
    (z : finiteGlobalTensorModel hπ data F (j + 1) hj)
    (hz : z ∈ Set.range g) (hs : z ∈ (p).smoothLocus) :
    z ∈ Set.range b ∨ z ∈ Set.range terminal := by
  have hg : Set.range (olderGlobalTensorChart hπ data F j hj 0 hj) = Set.range g := by
    rw [olderGlobalTensorChart_zero_retention]
  have h : z ∈ Set.range b ∪ Set.range c := by
    rw [retainedExterior_smooth_boundary_cover A hπ data D j hj 0 hj hk0 hk, hg]
    exact ⟨hz, hs⟩
  exact h.imp_right (fun hc =>
    lastConicBoundary_range_subset_terminal A hπ data D j hj hk0 hk hc)

end FLT.Mazur.WeierstrassDividedDepth

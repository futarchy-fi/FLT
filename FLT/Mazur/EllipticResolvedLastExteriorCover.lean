/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteTensorAtlasTransport
public import FLT.Mazur.EllipticResolvedExteriorBoundaryCover
public import FLT.Mazur.EllipticResolvedTerminalCover
public import FLT.Mazur.EllipticRetainedTerminalBoundaryCover

/-!
# The final positive-depth exterior in the original resolved fiber

Transport the last conic inclusion into the actual terminal atlas member.
This covers its entire smooth restriction for both terminal parities.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)

section Transport
variable {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
  (r : ℕ) (hr : j + 1 + r ≤ n) (m : ℕ) (hm : m ≤ n)
  (he : j + 1 + r = m) (hlast : j + 1 = m)

include hlast in
/-- The last conic inclusion survives equal-stage transport with a zero retention count. -/
theorem lastConicBoundary_final_range_subset :
    Set.range (olderGlobalConicBoundary hπ data D j hj r hr hk0 hk ≫
      (finiteTensorIndexIso A hπ data (ResidueField A) (j + 1 + r) m hr hm he).hom) ⊆
    Set.range (globalDividedTensorChart hπ data (ResidueField A) m hm) := by
  have hr0 : r = 0 := by omega
  subst r
  subst m
  simpa only [finiteTensorIndexIso, Iso.refl_hom, Category.comp_id] using
    lastConicBoundary_range_subset_terminal A hπ data D j hj hk0 hk
end Transport

variable {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (j : ℕ) (hj0 : 0 < j) (hj : j < depth / 2) (hlast : j + 1 = depth / 2)
local notation "F" => ResidueField A
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "terminal" => globalDividedTensorChart hπ data F (depth / 2) (le_refl _)

include hlast in
/-- The complete last conic boundary lies in the actual terminal chart at final depth. -/
theorem resolvedLastConicChart_range_subset_terminal :
    Set.range (resolvedRetainedConicChart A D j hj0 hj) ⊆ Set.range terminal := by
  exact lastConicBoundary_final_range_subset A hπ data D j (by omega) (by omega)
    (by omega) (depth / 2 - (j + 1)) (by omega) (depth / 2) (le_refl _)
    (by omega) hlast

include hlast hj0 in
/-- Every smooth point of the final exterior lies in its boundary or the terminal atlas member. -/
theorem resolvedLastExterior_smooth_cover (z : resolvedSplitFiber A D)
    (hz : z ∈ Set.range (resolvedRetainedExteriorChart A D j hj))
    (hs : z ∈ (resolvedSplitStructure A D).smoothLocus) :
    z ∈ Set.range (resolvedRetainedBoundaryChart A D j hj) ∨
      z ∈ Set.range (globalTensorAtlasMap hπ data F (depth / 2) (le_refl _) (Fin.succ 0)) := by
  have h : z ∈ Set.range (resolvedRetainedBoundaryChart A D j hj) ∪
      Set.range (resolvedRetainedConicChart A D j hj0 hj) := by
    rw [resolvedRetainedExterior_smooth_boundary_cover]
    exact ⟨hz, hs⟩
  rcases h with hb | hc
  · exact Or.inl hb
  · apply Or.inr
    rw [← resolvedTerminalTensorChart_range A D]
    exact resolvedLastConicChart_range_subset_terminal A D j hj0 hj hlast hc

end FLT.Mazur.WeierstrassDividedDepth

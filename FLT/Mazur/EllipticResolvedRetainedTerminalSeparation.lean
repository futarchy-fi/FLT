/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedRetainedDepthSeparation
public import FLT.Mazur.WeierstrassDividedEarlierTerminalSeparation

/-!
# Every retained arithmetic boundary misses the terminal chart

The last boundary is separated by the original incidence equation. All earlier
boundaries lie in atlas members already disjoint from the full terminal chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)

section Last
variable {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (hp : algebraMap A (ResidueField A) π = 0)
local notation "F" => ResidueField A
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "t" => WeierstrassSuccessiveX.coord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "u" => WeierstrassSuccessiveX.coord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 2

include hp in
/-- The entire last arithmetic boundary misses the terminal divided tensor chart. -/
theorem lastRetainedBoundary_terminal_disjoint :
    Disjoint (Set.range (finiteRetainedBoundaryTensorChart A hπ data j hj 0 hj F))
      (Set.range (globalDividedTensorChart hπ data F (j + 1) hj)) := by
  rw [finiteRetainedBoundaryTensorChart_range, olderGlobalTensorChart_zero_retention]
  apply Set.disjoint_left.mpr
  rintro z ⟨x, rfl⟩ hx
  have ht : PrincipalOpenTensor.inclusion F u x ∈
      Set.range (PrincipalOpenTensor.inclusion F t) := by
    rw [← globalTensor_depthOverlap_preimage hπ data F j hj]
    exact hx
  exact Set.disjoint_left.mp
    (WeierstrassSuccessiveX.tensorBoundary_disjoint W (π ^ (start + j)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) F hp) ht ⟨x, rfl⟩

include hp in
/-- The last-boundary exclusion retains the actual final target transport. -/
theorem lastRetainedBoundary_final_terminal_disjoint
    (r m : ℕ) (hr : j + 1 + r ≤ n) (hm : m ≤ n)
    (he : j + 1 + r = m) (hlast : j + 1 = m) :
    Disjoint (Set.range (finiteRetainedBoundaryTensorChart A hπ data j hj r hr F ≫
      (finiteTensorIndexIso A hπ data F (j + 1 + r) m hr hm he).hom))
      (Set.range (globalDividedTensorChart hπ data F m hm)) := by
  have hr0 : r = 0 := by omega
  subst r
  subst m
  simpa only [finiteTensorIndexIso, Iso.refl_hom, Category.comp_id] using
    lastRetainedBoundary_terminal_disjoint A hπ data j hj hp
end Last

variable {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
local notation "F" => ResidueField A
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D

/-- Every full retained arithmetic boundary is disjoint from the entire terminal tensor chart. -/
theorem resolvedRetainedBoundary_terminal_disjoint (j : ℕ) (hj : j < depth / 2) :
    Disjoint (Set.range (resolvedRetainedBoundaryChart A D j hj))
      (Set.range (globalDividedTensorChart hπ data F (depth / 2) (le_refl _))) := by
  have hp : algebraMap A F π = 0 := (residue_eq_zero_iff π).mpr
    (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
  by_cases hlast : j + 1 = depth / 2
  · exact lastRetainedBoundary_final_terminal_disjoint A hπ data j (by omega) hp
      (depth / 2 - (j + 1)) (depth / 2) (by omega) (le_refl _) (by omega) hlast
  · have hd := globalTensorAtlas_terminal_nonadjacent_disjoint hπ data F
      (depth / 2) (le_refl _) hp ⟨depth / 2 - j + 1, by omega⟩ (by dsimp; omega)
    apply hd.mono_left
    have hs := resolvedRetainedBoundaryChart_range_fixed A D j hj
    rw [retainedTensorChartAt_range_index] at hs
    exact hs

end FLT.Mazur.WeierstrassDividedDepth

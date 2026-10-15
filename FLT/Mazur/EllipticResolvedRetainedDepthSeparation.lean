/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedPositiveExteriorCoverage
public import FLT.Mazur.EllipticResolvedZeroExteriorCover
public import FLT.Mazur.WeierstrassSuccessiveXTensorBoundarySeparation
public import FLT.Mazur.WeierstrassDividedFinalNodeNonadjacent

/-!
# Geometric separation of the retained arithmetic boundaries

Adjacent boundaries are opposite principal opens in one original exterior.
Nonadjacent boundaries lie in already disjoint original atlas members.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
local notation "F" => ResidueField A
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D

section Transport
variable {U : WeierstrassCurve A} {ϖ : A} (hϖ : ϖ ≠ 0) {start n : ℕ}
  (ds : (i : Fin (n + 1)) → Data U ϖ (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
  (m : ℕ) (hm : m ≤ n) (he : j + 1 + r = m)
local notation "e" => ds (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "u" => WeierstrassSuccessiveX.coord U (ϖ ^ (start + j)) ϖ
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "E" => finiteTensorIndexIso A hϖ ds F (j + 1 + r) m hr hm he

/-- Equal final-stage transport retains the full horizontal boundary image. -/
theorem retainedBoundary_final_range_horizontal :
    Set.range (finiteRetainedBoundaryTensorChart A hϖ ds j hj r hr F ≫ (E).hom) =
      Set.range (PrincipalOpenTensor.inclusion F u ≫
        (olderGlobalTensorChart hϖ ds F j hj r hr ≫ (E).hom)) := by
  subst m
  simpa only [finiteTensorIndexIso, Iso.refl_hom, Category.comp_id] using
    finiteRetainedBoundaryTensorChart_range A hϖ ds j hj r hr F
end Transport

section Boundary
variable (j : ℕ) (hj : j < depth / 2)
local notation "r" => depth / 2 - (j + 1)
local notation "E" => finiteTensorIndexIso A hπ data F
  (j + 1 + r) (depth / 2) (by omega) (le_refl _) (by omega)
local notation "e" => data (Fin.mk (j + 1) (by omega))
local notation "u" => WeierstrassSuccessiveX.coord W (π ^ (0 + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "g" => olderGlobalTensorChart hπ data F j (by omega) r (by omega)

/-- The full retained boundary keeps its original horizontal principal-open image. -/
theorem resolvedRetainedBoundaryChart_range_horizontal :
    Set.range (resolvedRetainedBoundaryChart A D j hj) =
      Set.range (PrincipalOpenTensor.inclusion F u ≫ resolvedRetainedExteriorChart A D j hj) := by
  exact retainedBoundary_final_range_horizontal A hπ data j (by omega) r (by omega)
    (depth / 2) (le_refl _) (by omega)

/-- The complete retained boundary lies in its actual fixed-stage tensor chart. -/
theorem resolvedRetainedBoundaryChart_range_fixed :
    Set.range (resolvedRetainedBoundaryChart A D j hj) ⊆
      Set.range (retainedTensorChartAt hπ data (depth / 2) (le_refl _) j (by omega)) := by
  rw [resolvedRetainedBoundaryChart_range_horizontal]
  rw [retainedTensorChartAt_range_index]
  rintro z ⟨x, rfl⟩
  have hx : (PrincipalOpenTensor.inclusion F u ≫
      resolvedRetainedExteriorChart A D j hj) x ∈
      Set.range (resolvedRetainedExteriorChart A D j hj) := ⟨_, rfl⟩
  rw [resolvedRetainedExteriorChart_range_index A D j hj
    ⟨depth / 2 - j + 1, by omega⟩ (by dsimp; omega)] at hx
  exact hx

/-- The two original boundary opens remain disjoint in the final resolved fiber. -/
theorem resolvedRetainedBoundary_incidence_disjoint :
    Disjoint (Set.range (resolvedRetainedBoundaryChart A D j hj))
      (Set.range (resolvedRetainedIncidenceChart A D j hj)) := by
  rw [resolvedRetainedBoundaryChart_range_horizontal]
  have hp : algebraMap A F π = 0 := (residue_eq_zero_iff π).mpr
    (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
  have hd := (WeierstrassSuccessiveX.tensorBoundary_disjoint W (π ^ (0 + j)) π
    (Data.b3 e) (Data.b4 e) (Data.b6 e) F hp).symm
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx⟩ ⟨y, hy⟩
  have he := (resolvedRetainedExteriorChart A D j hj).isOpenEmbedding.injective
    (hx.trans hy.symm)
  exact Set.disjoint_left.mp hd ⟨x, rfl⟩ ⟨y, he.symm⟩

/-- Every two adjacent retained arithmetic boundaries have disjoint full images. -/
theorem resolvedRetainedBoundary_adjacent_disjoint (hn : j + 1 < depth / 2) :
    Disjoint (Set.range (resolvedRetainedBoundaryChart A D j hj))
      (Set.range (resolvedRetainedBoundaryChart A D (j + 1) hn)) := by
  rw [← resolvedRetainedIncidenceChart_range_eq_next A D j hj hn]
  exact resolvedRetainedBoundary_incidence_disjoint A D j hj
end Boundary

/-- Distinct retained depths have disjoint arithmetic boundary images, including depth zero. -/
theorem resolvedRetainedBoundary_depth_disjoint (a b : ℕ)
    (ha : a < depth / 2) (hb : b < depth / 2) (hab : a ≠ b) :
    Disjoint (Set.range (resolvedRetainedBoundaryChart A D a ha))
      (Set.range (resolvedRetainedBoundaryChart A D b hb)) := by
  suffices H : ∀ a b (ha : a < depth / 2) (hb : b < depth / 2), a < b →
      Disjoint (Set.range (resolvedRetainedBoundaryChart A D a ha))
        (Set.range (resolvedRetainedBoundaryChart A D b hb)) by
    rcases lt_or_gt_of_ne hab with h | h
    · exact H a b ha hb h
    · exact (H b a hb ha h).symm
  intro a b ha hb h
  by_cases he : b = a + 1
  · subst b
    exact resolvedRetainedBoundary_adjacent_disjoint A D a ha hb
  · exact (retainedTensorChartAt_nonadjacent_disjoint hπ data D
      (depth / 2) (le_refl _) a b (by omega) (by omega)).mono
      (resolvedRetainedBoundaryChart_range_fixed A D a ha)
      (resolvedRetainedBoundaryChart_range_fixed A D b hb)

end FLT.Mazur.WeierstrassDividedDepth

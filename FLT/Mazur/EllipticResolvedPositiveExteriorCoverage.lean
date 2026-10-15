/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedAdjacentBoundaryCover
public import FLT.Mazur.EllipticResolvedComponentAtlasCoverage
public import FLT.Mazur.EllipticResolvedLastExteriorCover
public import FLT.Mazur.WeierstrassDividedInitialZeroInfinity

/-!
# Arithmetic coverage of all positive-depth exteriors

Every smooth point in a positive-depth exterior belongs to the actual
arithmetic component family. After discarding the redundant initial slope
chart, only the first, zero-depth retained exterior can remain uncovered.
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
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "p" => resolvedSplitStructure A D
local notation "inc" => Scheme.Opens.ι (Scheme.Hom.smoothLocus (resolvedSplitStructure A D))
local notation "chart" => resolvedComponentChart A D r

/-- The entire original positive-depth exterior is covered by the arithmetic component family. -/
theorem resolvedComponentCharts_cover_positive_exterior (j : ℕ) (hj0 : 0 < j)
    (hj : j < depth / 2) (z : (p).smoothLocus.toScheme)
    (hz : inc z ∈ Set.range (resolvedRetainedExteriorChart A D j hj)) :
    ∃ i, z ∈ Set.range (chart i) := by
  by_cases hn : j + 1 < depth / 2
  · have h : inc z ∈ Set.range (resolvedRetainedBoundaryChart A D j hj) ∪
        Set.range (resolvedRetainedBoundaryChart A D (j + 1) hn) := by
      rw [resolvedRetainedExterior_smooth_adjacent_cover A D j hj0 hj hn]
      exact ⟨hz, z.property⟩
    exact h.elim (resolvedComponentCharts_cover_retained A D r j hj0 hj z)
      (resolvedComponentCharts_cover_retained A D r (j + 1) (by omega) hn z)
  · have h := resolvedLastExterior_smooth_cover A D j hj0 hj (by omega)
      (inc z) hz z.property
    exact h.elim (resolvedComponentCharts_cover_retained A D r j hj0 hj z)
      (resolvedComponentCharts_cover_terminal A D r (by omega) z)

/-- Final-stage transport identifies the exterior with its precise original atlas image. -/
theorem resolvedRetainedExteriorChart_range_index (j : ℕ) (hj : j < depth / 2)
    (i : Fin (depth / 2 + 3)) (hi : depth / 2 - (j + 1) + 2 = i.val) :
    Set.range (resolvedRetainedExteriorChart A D j hj) =
      Set.range (globalTensorAtlasMap hπ data F (depth / 2) (le_refl _) i) :=
  finiteTensorIndexIso_older_range A hπ data F (le_refl _) j
    (depth / 2 - (j + 1)) (by omega) (by omega) (by omega) i hi

/-- Any uncovered smooth point at positive final stage lies in the zero-depth exterior. -/
theorem resolvedComponentCharts_uncovered_zero_exterior (hk0 : 0 < depth / 2)
    (z : (p).smoothLocus.toScheme) (hz : ¬ ∃ i, z ∈ Set.range (chart i)) :
    inc z ∈ Set.range (globalTensorAtlasMap hπ data F (depth / 2) (le_refl _)
      ⟨depth / 2 + 1, by omega⟩) := by
  obtain ⟨i, x, hi, hx⟩ := zeroStartAtlas_cover_without_initial hπ data D
    (by omega) rfl (depth / 2) (le_refl _) (inc z)
  by_cases h0 : i.val = 0
  · have he : i = 0 := Fin.ext h0
    subst i
    exact (hz (resolvedComponentCharts_cover_infinity A D r z ⟨x, hx⟩)).elim
  by_cases h1 : i.val = 1
  · have he : i = Fin.succ 0 := Fin.ext h1
    subst i
    exact (hz (resolvedComponentCharts_cover_terminal A D r hk0 z ⟨x, hx⟩)).elim
  by_cases hi' : i.val = depth / 2 + 1
  · have he : i = ⟨depth / 2 + 1, Nat.add_lt_add_left (by decide : 1 < 3) _⟩ :=
      Fin.ext hi'
    subst i
    exact ⟨x, hx⟩
  have hj : depth / 2 + 1 - i.val < depth / 2 := by omega
  have hc : inc z ∈ Set.range
      (resolvedRetainedExteriorChart A D (depth / 2 + 1 - i.val) hj) := by
    rw [resolvedRetainedExteriorChart_range_index A D _ hj i (by omega)]
    exact ⟨x, hx⟩
  exact (hz (resolvedComponentCharts_cover_positive_exterior A D r _ (by omega) hj z hc)).elim

end FLT.Mazur.WeierstrassDividedDepth

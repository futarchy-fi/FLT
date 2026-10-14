/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedComponentCharts
public import FLT.Mazur.EllipticResolvedRetainedCover
public import FLT.Mazur.EllipticResolvedTerminalCover
public import FLT.Mazur.WeierstrassDividedInfinitySmoothCompatibility

/-!
# Geometric coverage by the assembled original component family

The actual smooth points in the infinity, retained boundary, and terminal
atlas opens belong to the assembled arithmetic component family. At positive
final stage any uncovered smooth point lies in a remaining exterior atlas member.
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

/-- Passing to the smooth open preserves membership in the image of any component chart. -/
theorem resolvedComponentChart_mem_range_iff (i : ResolvedComponentIndex depth)
    (z : (p).smoothLocus.toScheme) :
    z ∈ Set.range (chart i) ↔ inc z ∈ Set.range (chart i ≫ inc) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (inc).isOpenEmbedding.injective hx⟩

/-- The full infinity atlas member is covered by the assembled identity chart. -/
theorem resolvedComponentCharts_cover_infinity (z : (p).smoothLocus.toScheme)
    (hz : inc z ∈ Set.range (finiteInfinityTensorChart hπ data F (depth / 2) (le_refl _))) :
    ∃ i, z ∈ Set.range (chart i) := by
  refine ⟨.identity, ?_⟩
  rw [resolvedComponentChart_mem_range_iff]
  change inc z ∈ Set.range (resolvedIdentitySmoothChart A D ≫ inc)
  rw [resolvedIdentitySmoothChart_inclusion, resolvedIdentityChart_range_infinity]
  exact hz

/-- Every geometric point of a retained boundary is covered by its two arithmetic labels. -/
theorem resolvedComponentCharts_cover_retained (j : ℕ) (hj0 : 0 < j)
    (hj : j < depth / 2) (z : (p).smoothLocus.toScheme)
    (hz : inc z ∈ Set.range (resolvedRetainedBoundaryChart A D j hj)) :
    ∃ i, z ∈ Set.range (chart i) := by
  rw [← resolvedRetainedCharts_cover A D r j hj0 hj] at hz
  rcases hz with hn | hp
  · refine ⟨.retainedNegative j hj0 hj, ?_⟩
    rw [resolvedComponentChart_mem_range_iff]
    change inc z ∈ Set.range (resolvedRetainedNegativeSmoothChart A D r j hj0 hj ≫ inc)
    rw [resolvedRetainedNegativeSmoothChart_inclusion]
    exact hn
  · refine ⟨.retainedPositive j hj0 hj, ?_⟩
    rw [resolvedComponentChart_mem_range_iff]
    change inc z ∈ Set.range (resolvedRetainedPositiveSmoothChart A D r j hj0 hj ≫ inc)
    rw [resolvedRetainedPositiveSmoothChart_inclusion]
    exact hp

/-- The complete smooth restriction of the terminal atlas member has arithmetic component charts. -/
theorem resolvedComponentCharts_cover_terminal (hk0 : 0 < depth / 2)
    (z : (p).smoothLocus.toScheme)
    (hz : inc z ∈ Set.range (globalTensorAtlasMap hπ data F
      (depth / 2) (le_refl _) (Fin.succ 0))) : ∃ i, z ∈ Set.range (chart i) := by
  rw [← resolvedTerminalTensorChart_range A D] at hz
  rcases lt_or_eq_of_le (show 2 * (depth / 2) ≤ depth by omega) with hp | hm
  · have h : inc z ∈ Set.range (resolvedTerminalNegativeChart A D r hk0 hp) ∪
        Set.range (resolvedTerminalPositiveChart A D r hk0 hp) := by
      rw [resolvedTerminalCharts_cover]
      exact ⟨hz, z.property⟩
    rcases h with hn | hp'
    · refine ⟨.terminalNegative hk0 hp, ?_⟩
      rw [resolvedComponentChart_mem_range_iff]
      change inc z ∈ Set.range (resolvedTerminalNegativeSmoothChart A D r hk0 hp ≫ inc)
      rw [resolvedTerminalNegativeSmoothChart_inclusion]
      exact hn
    · refine ⟨.terminalPositive hk0 hp, ?_⟩
      rw [resolvedComponentChart_mem_range_iff]
      change inc z ∈ Set.range (resolvedTerminalPositiveSmoothChart A D r hk0 hp ≫ inc)
      rw [resolvedTerminalPositiveSmoothChart_inclusion]
      exact hp'
  · refine ⟨.terminalMiddle hk0 hm, ?_⟩
    rw [resolvedComponentChart_mem_range_iff]
    change inc z ∈ Set.range (resolvedTerminalMiddleSmoothChart A D r hk0 hm ≫ inc)
    rw [resolvedTerminalMiddleSmoothChart_inclusion, resolvedTerminalMiddleChart_range]
    exact hz

/-- Any remaining uncovered smooth point lies in an original exterior atlas member. -/
theorem resolvedComponentCharts_uncovered_exterior (hk0 : 0 < depth / 2)
    (z : (p).smoothLocus.toScheme) (hz : ¬ ∃ i, z ∈ Set.range (chart i)) :
    ∃ i : Fin (depth / 2 + 1),
      inc z ∈ Set.range (globalTensorAtlasMap hπ data F (depth / 2) (le_refl _) i.succ.succ) := by
  obtain ⟨i, x, hx⟩ := globalTensorAtlas_cover hπ data F (depth / 2) (le_refl _) (inc z)
  cases i using Fin.cases with
  | zero => exact (hz (resolvedComponentCharts_cover_infinity A D r z ⟨x, hx⟩)).elim
  | succ i =>
    cases i using Fin.cases with
    | zero => exact (hz (resolvedComponentCharts_cover_terminal A D r hk0 z ⟨x, hx⟩)).elim
    | succ i => exact ⟨i, x, hx⟩

end FLT.Mazur.WeierstrassDividedDepth

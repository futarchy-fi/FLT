/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedPositiveStageCoverage
public import FLT.Mazur.WeierstrassDividedTensorInfinityPreimage
public import FLT.Mazur.WeierstrassDilatationZeroResidueSmoothY

/-!
# Complete smooth-chart coverage at the zero final stage

At depth one the terminal nodal chart contributes only points already in infinity.
Combining this with positive-stage coverage gives the full arithmetic component cover.
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
local notation "g" => globalDividedTensorChart hπ data F (depth / 2) (le_refl _)
local notation "d" => data (Fin.mk (depth / 2) (Nat.lt_succ_self _))
local notation "inc" => Scheme.Opens.ι (Scheme.Hom.smoothLocus (resolvedSplitStructure A D))
local notation "chart" => resolvedComponentChart A D r

/-- At zero final stage every smooth terminal point belongs to the original infinity chart. -/
theorem resolvedZeroStage_terminal_subset_infinity (hk : depth / 2 = 0)
    {z : resolvedSplitFiber A D} (hz : z ∈ Set.range g) (hs : z ∈ (p).smoothLocus) :
    z ∈ Set.range (finiteInfinityTensorChart hπ data F (depth / 2) (le_refl _)) := by
  obtain ⟨x, rfl⟩ := hz
  have hy := WeierstrassDilatation.zeroResidue_smooth_y D D.depth_pos (0 + depth / 2)
    (by omega) (Data.b3 d) (Data.b4 d) (Data.b6 d)
    (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) g p
    (globalDividedTensorChart_structure hπ data F (depth / 2) (le_refl _)) x hs
  have he := globalDividedTensor_zero_infinity hπ data F (depth / 2) (le_refl _)
    (by omega)
  exact Set.ext_iff.mp he x |>.mpr hy

/-- The identity arithmetic chart covers the whole resolved smooth fiber at depth one. -/
theorem resolvedZeroStage_identity_covers (hk : depth / 2 = 0)
    (z : (p).smoothLocus.toScheme) : z ∈ Set.range (chart .identity) := by
  have hi : inc z ∈ Set.range
      (finiteInfinityTensorChart hπ data F (depth / 2) (le_refl _)) := by
    obtain ⟨i, x, hi, hx⟩ := zeroStartAtlas_cover_without_initial hπ data D
      D.depth_pos rfl (depth / 2) (le_refl _) (inc z)
    by_cases h0 : i.val = 0
    · have he : i = 0 := Fin.ext h0
      subst i
      exact ⟨x, hx⟩
    · have he : i = Fin.succ 0 := Fin.ext (by simp only [Fin.val_succ, Fin.val_zero]; omega)
      subst i
      apply resolvedZeroStage_terminal_subset_infinity A D hk _ z.property
      rw [resolvedTerminalTensorChart_range]
      exact ⟨x, hx⟩
  rw [resolvedComponentChart_mem_range_iff]
  change inc z ∈ Set.range (resolvedIdentitySmoothChart A D ≫ inc)
  rw [resolvedIdentitySmoothChart_inclusion, resolvedIdentityChart_range_infinity]
  exact hi

/-- The actual arithmetic component family covers all geometric points of the smooth fiber. -/
theorem resolvedComponentCharts_cover (z : (p).smoothLocus.toScheme) :
    ∃ i, z ∈ Set.range (chart i) := by
  rcases Nat.eq_zero_or_pos (depth / 2) with h | h
  · exact ⟨.identity, resolvedZeroStage_identity_covers A D r h z⟩
  · exact resolvedComponentCharts_cover_positive_stage A D r h z

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteGeneralizedCurve
public import FLT.Mazur.PolygonCompleteGenericRelativeDimension

/-!
# Relative dimension of the entire complete polygon smooth group

Closed smooth points and points avoiding the parameter give dimension-one
neighborhoods covering the full smooth locus, over the original complete base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] exactVeroneseProjToBase_lfp PolygonPinching.cyclic_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "f" => exactVeroneseProjToBase K n h

/-- Every smooth point of the entire complete family has a relative-curve neighborhood. -/
theorem completeSmooth_exists_dimensionOpen (x : exactVeroneseProj K n h)
    (hx : x ∈ (f).smoothLocus) :
    ∃ V : (exactVeroneseProj K n h).Opens, x ∈ V ∧
      SmoothOfRelativeDimension 1 (V.ι ≫ (f)) := by
  by_cases ht : PowerSeries.X ∈ ((f) x).asIdeal
  · have hb : (f) x = IsLocalRing.closedPoint (PowerSeries K) := by
      apply PrimeSpectrum.ext
      symm
      change IsLocalRing.maximalIdeal (PowerSeries K) = ((f) x).asIdeal
      apply Ideal.IsMaximal.eq_of_le inferInstance ((f) x).isPrime.ne_top
      rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_le_iff_mem]
      exact ht
    have hr : x ∈ Set.range (completeClosedFiberInclusion K n h) := by
      rw [completeClosedFiber_range]
      exact hb
    obtain ⟨y, rfl⟩ := hr
    exact completeClosedSmooth_exists_dimensionOpen K n h y
      ((completeClosedFiber_mem_smoothLocus K n h y).mp hx)
  · exact complete_exists_dimensionOpen_of_parameter_notMem K n h x ht

/-- The actual entire smooth open has relative dimension one over the complete coefficient ring. -/
theorem completeSmoothLocus_relativeDimension :
    SmoothOfRelativeDimension 1 ((f).smoothLocus.ι ≫ (f)) := by
  let U := (f).smoothLocus
  have hd := fun x : U.toScheme ↦ completeSmooth_exists_dimensionOpen K n h x.1 x.2
  choose V hx hV using hd
  have hc : (⨆ x, U.ι ⁻¹ᵁ V x) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1)
    (fun x ↦ U.ι ⁻¹ᵁ V x) hc
  intro x
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension 1) (hV x) _

/-- The constructed generalized curve's whole smooth group has relative dimension one. -/
instance completeGeneralizedGroup_relativeDimension :
    SmoothOfRelativeDimension 1 (completeGeneralizedCurve K n h).group.hom :=
  completeSmoothLocus_relativeDimension K n h

end FLT.Mazur.PolygonInfinitesimalStages

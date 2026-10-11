/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedSingularPoints
public import FLT.Mazur.PolygonCompleteClosedSpecialization
public import FLT.Mazur.PolygonCompleteNodeGenerizationSmooth

/-!
# Smoothness of the actual complete polygon away from its original parameter

Properness specializes every point into the original polygon. Smooth
specializations are already smooth in the total family, and the only
remaining specializations are the actual nodes, whose punctured stalks
are formally smooth. Thus every base change inverting q is smooth.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] exactVeroneseProjToBase_lfp

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Every actual total-space point avoiding the original parameter is smooth. -/
theorem complete_mem_smoothLocus_of_parameter_notMem (y : exactVeroneseProj K n h)
    (ht : PowerSeries.X ∉ ((exactVeroneseProjToBase K n h) y).asIdeal) :
    y ∈ (exactVeroneseProjToBase K n h).smoothLocus := by
  obtain ⟨x, hy⟩ := exists_completeClosedFiber_specialization K n h y
  by_cases hx : completeClosedFiberInclusion K n h x ∈
      (exactVeroneseProjToBase K n h).smoothLocus
  · exact hy.mem_open (exactVeroneseProjToBase K n h).smoothLocus.isOpen hx
  · obtain ⟨i, hi⟩ := completeClosedFiber_nonsmooth_eq_node K n h x hx
    rw [hi] at hy
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      (exactVeroneseProj K n h).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (completeNode K n h i)) isOpen_univ
    exact completeNodeGenerization_mem_smoothLocus K n h i ⟨U, hU⟩ hxU y hy ht

/-- The actual complete family is smooth after any coefficient change making q a unit. -/
theorem completeBaseChange_smooth_of_parameter_isUnit
    (S : Type) [CommRing S] [Algebra (PowerSeries K) S]
    (ht : IsUnit (algebraMap (PowerSeries K) S PowerSeries.X)) :
    Smooth (pullback.snd (exactVeroneseProjToBase K n h)
      (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) S)))) := by
  let _ := exactVeroneseProjToBase_flat K n h
  rw [← Scheme.Hom.smoothLocus_eq_top_iff,
    ← Scheme.Hom.preimage_smoothLocus_baseChange]
  apply top_le_iff.mp
  intro z _
  apply complete_mem_smoothLocus_of_parameter_notMem
  have he := congrArg (fun g ↦ g z) (pullback.condition
    (f := exactVeroneseProjToBase K n h)
    (g := Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) S))))
  simp only [Scheme.Hom.comp_apply] at he
  rw [he]
  exact (pullback.snd (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) S))) z).asIdeal.notMem_of_isUnit ht

/-- The actual generic fiber is smooth over any chosen fraction field. -/
theorem completeGenericFiber_smooth
    (F : Type) [Field F] [Algebra (PowerSeries K) F] [IsFractionRing (PowerSeries K) F] :
    Smooth (pullback.snd (exactVeroneseProjToBase K n h)
      (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) F)))) := by
  apply completeBaseChange_smooth_of_parameter_isUnit
  apply isUnit_iff_ne_zero.mpr
  simpa only [map_zero] using
    (IsFractionRing.injective (PowerSeries K) F).ne PowerSeries.X_ne_zero

end FLT.Mazur.PolygonInfinitesimalStages

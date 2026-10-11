/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedSingularPoints
public import FLT.Mazur.PolygonCompleteClosedSpecialization
public import FLT.Mazur.PolygonCompleteNodeDimensionOpen
public import FLT.Mazur.PolygonCompleteSmoothDimensionOpen
public import FLT.Mazur.RelativeDimensionBaseChangeOpen

/-!
# Relative dimension of the actual generic polygon family

Proper specialization reduces each parameter-nonzero point to either a smooth
point of the original polygon or an actual complete node. Both cases now yield
relative-curve opens, which cover every coefficient change inverting the parameter.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] exactVeroneseProjToBase_lfp PolygonPinching.cyclic_lfp

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Every actual point avoiding the original parameter has a relative-curve neighborhood. -/
theorem complete_exists_dimensionOpen_of_parameter_notMem (y : exactVeroneseProj K n h)
    (ht : PowerSeries.X ∉ ((exactVeroneseProjToBase K n h) y).asIdeal) :
    ∃ V : (exactVeroneseProj K n h).Opens, y ∈ V ∧
      SmoothOfRelativeDimension 1 (V.ι ≫ exactVeroneseProjToBase K n h) := by
  obtain ⟨x, hy⟩ := exists_completeClosedFiber_specialization K n h y
  by_cases hx : completeClosedFiberInclusion K n h x ∈
      (exactVeroneseProjToBase K n h).smoothLocus
  · exact completeClosedSmoothGenerization_exists_dimensionOpen K n h x
      ((completeClosedFiber_mem_smoothLocus K n h x).mp hx) y hy
  · obtain ⟨i, hi⟩ := completeClosedFiber_nonsmooth_eq_node K n h x hx
    rw [hi] at hy
    exact completeNodeGenerization_exists_dimensionOpen K n h i y hy ht

/-- Coefficient changes inverting the original parameter have relative dimension one. -/
theorem completeBaseChange_relativeDimension_of_parameter_isUnit
    (S : Type) [CommRing S] [Algebra (PowerSeries K) S]
    (ht : IsUnit (algebraMap (PowerSeries K) S PowerSeries.X)) :
    SmoothOfRelativeDimension 1 (pullback.snd (exactVeroneseProjToBase K n h)
      (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) S)))) := by
  apply RelativeDimensionBaseChangeOpen.of_exists_open
  intro z
  apply complete_exists_dimensionOpen_of_parameter_notMem
  have he := congrArg (fun g ↦ g z) (pullback.condition
    (f := exactVeroneseProjToBase K n h)
    (g := Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) S))))
  simp only [Scheme.Hom.comp_apply] at he
  rw [he]
  exact (pullback.snd (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) S))) z).asIdeal.notMem_of_isUnit ht

/-- The original generic fiber is smooth of relative dimension one over any fraction field. -/
theorem completeGenericFiber_relativeDimension
    (F : Type) [Field F] [Algebra (PowerSeries K) F] [IsFractionRing (PowerSeries K) F] :
    SmoothOfRelativeDimension 1 (pullback.snd (exactVeroneseProjToBase K n h)
      (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) F)))) := by
  apply completeBaseChange_relativeDimension_of_parameter_isUnit
  apply isUnit_iff_ne_zero.mpr
  simpa only [map_zero] using
    (IsFractionRing.injective (PowerSeries K) F).ne PowerSeries.X_ne_zero

end FLT.Mazur.PolygonInfinitesimalStages

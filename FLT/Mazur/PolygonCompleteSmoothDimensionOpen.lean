/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedSmoothLocus
public import FLT.Mazur.PolygonSmoothRelativeDimension
public import FLT.Mazur.SmoothBaseChangeDimensionOpen

/-!
# Dimension opens at smooth closed points of the original complete polygon

The actual polygon smooth locus computes the dimension on the original
complete family's smooth charts. The resulting opens contain all generizations
of the chosen smooth closed-fiber point.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local irreducible] originalStageToCompatibleProj
attribute [local instance] exactVeroneseProjToBase_lfp PolygonPinching.cyclic_lfp

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- A smooth original polygon point has a relative-curve open in the actual complete family. -/
theorem completeClosedSmooth_exists_dimensionOpen (x : PolygonCyclicAtlas.scheme K n h)
    (hx : x ∈ (PolygonCyclicAtlas.toBase K n h).smoothLocus) :
    ∃ V : (exactVeroneseProj K n h).Opens,
      completeClosedFiberInclusion K n h x ∈ V ∧
        SmoothOfRelativeDimension 1 (V.ι ≫ exactVeroneseProjToBase K n h) := by
  let _ := (PowerSeries.constantCoeff : PowerSeries K →+* K).toAlgebra
  let _ : SmoothOfRelativeDimension 1
      ((completeClosedFiberInclusion K n h ⁻¹ᵁ (exactVeroneseProjToBase K n h).smoothLocus).ι ≫
        PolygonCyclicAtlas.toBase K n h) := by
    rw [completeClosedFiber_preimage_smoothLocus]
    exact PolygonPinching.cyclic_smoothLocus_relativeDimension K n h
  exact SmoothBaseChangeDimensionOpen.exists_open_at_smoothPoint
    (exactVeroneseProjToBase K n h) (PolygonCyclicAtlas.toBase K n h)
    (completeClosedFiberInclusion K n h) (completeClosedFiber_isPullback K n h) 1 x
    ((completeClosedFiber_mem_smoothLocus K n h x).mpr hx)

/-- All generizations of a smooth closed-fiber point have actual relative-curve neighborhoods. -/
theorem completeClosedSmoothGenerization_exists_dimensionOpen
    (x : PolygonCyclicAtlas.scheme K n h)
    (hx : x ∈ (PolygonCyclicAtlas.toBase K n h).smoothLocus)
    (y : exactVeroneseProj K n h) (hy : y ⤳ completeClosedFiberInclusion K n h x) :
    ∃ V : (exactVeroneseProj K n h).Opens, y ∈ V ∧
      SmoothOfRelativeDimension 1 (V.ι ≫ exactVeroneseProjToBase K n h) := by
  obtain ⟨V, hxV, hd⟩ := completeClosedSmooth_exists_dimensionOpen K n h x hx
  exact ⟨V, hy.mem_open V.isOpen hxV, hd⟩

end FLT.Mazur.PolygonInfinitesimalStages

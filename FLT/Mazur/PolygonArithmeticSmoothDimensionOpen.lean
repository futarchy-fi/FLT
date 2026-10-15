/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticClosedSmoothLocus
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

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local irreducible] originalStageToCompatibleProj
attribute [local instance] exactVeroneseProjToBase_lfp PolygonPinching.cyclic_lfp

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]

local notation "K" => IsLocalRing.ResidueField A

/-- A smooth original polygon point has a relative-curve open in the actual complete family. -/
theorem completeClosedSmooth_exists_dimensionOpen (x : PolygonCyclicAtlas.scheme K n h)
    (hx : x ∈ (PolygonCyclicAtlas.toBase K n h).smoothLocus) :
    ∃ V : (exactVeroneseProj A π n h hne hgen).Opens,
      completeClosedFiberInclusion A π hne hgen n h x ∈ V ∧
        SmoothOfRelativeDimension 1 (V.ι ≫ exactVeroneseProjToBase A π n h hne hgen) := by
  let _ := (IsLocalRing.residue A).toAlgebra
  let _ : SmoothOfRelativeDimension 1
      ((completeClosedFiberInclusion A π hne hgen n h ⁻¹ᵁ
        (exactVeroneseProjToBase A π n h hne hgen).smoothLocus).ι ≫
        PolygonCyclicAtlas.toBase K n h) := by
    rw [completeClosedFiber_preimage_smoothLocus]
    exact PolygonPinching.cyclic_smoothLocus_relativeDimension K n h
  exact SmoothBaseChangeDimensionOpen.exists_open_at_smoothPoint
    (exactVeroneseProjToBase A π n h hne hgen) (PolygonCyclicAtlas.toBase K n h)
    (completeClosedFiberInclusion A π hne hgen n h)
    (completeClosedFiber_isPullback A π hne hgen n h) 1 x
    ((completeClosedFiber_mem_smoothLocus A π hne hgen n h x).mpr hx)

/-- All generizations of a smooth closed-fiber point have actual relative-curve neighborhoods. -/
theorem completeClosedSmoothGenerization_exists_dimensionOpen
    (x : PolygonCyclicAtlas.scheme K n h)
    (hx : x ∈ (PolygonCyclicAtlas.toBase K n h).smoothLocus)
    (y : exactVeroneseProj A π n h hne hgen)
    (hy : y ⤳ completeClosedFiberInclusion A π hne hgen n h x) :
    ∃ V : (exactVeroneseProj A π n h hne hgen).Opens, y ∈ V ∧
      SmoothOfRelativeDimension 1 (V.ι ≫ exactVeroneseProjToBase A π n h hne hgen) := by
  obtain ⟨V, hxV, hd⟩ := completeClosedSmooth_exists_dimensionOpen A π hne hgen n h x hx
  exact ⟨V, hy.mem_open V.isOpen hxV, hd⟩

end FLT.Mazur.PolygonArithmeticStages

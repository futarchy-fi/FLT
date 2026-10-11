/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedSmoothLocus

/-!
# Every actual complete-family point specializes into the original polygon

The original closed coefficient map has exactly the closed point as image.
Properness lifts specialization on the local power-series base, and the
cartesian original closed fiber supplies its actual polygon preimage.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original coefficient reduction has precisely the closed point as image. -/
theorem completeClosedBase_range :
    Set.range (completeClosedBase K) = {IsLocalRing.closedPoint (PowerSeries K)} := by
  let _ : IsLocalHom (PowerSeries.constantCoeff : PowerSeries K →+* K) :=
    ⟨fun a ha ↦ PowerSeries.isUnit_iff_constantCoeff.mpr ha⟩
  have he : completeClosedBase K (IsLocalRing.closedPoint K) =
      IsLocalRing.closedPoint (PowerSeries K) :=
    IsLocalRing.comap_closedPoint (PowerSeries.constantCoeff : PowerSeries K →+* K)
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    simpa only [Set.mem_singleton_iff, Subsingleton.elim z (IsLocalRing.closedPoint K)] using he
  · rintro rfl
    exact ⟨IsLocalRing.closedPoint K, he⟩

/-- The original polygon is exactly the inverse image of the original closed base point. -/
theorem completeClosedFiber_range :
    Set.range (completeClosedFiberInclusion K n h) =
      (exactVeroneseProjToBase K n h) ⁻¹' {IsLocalRing.closedPoint (PowerSeries K)} := by
  rw [← completeClosedFiberIso_fst]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (completeClosedFiberIso K n h).hom.surjective, Set.image_univ,
    Scheme.Pullback.range_fst, completeClosedBase_range]

/-- Properness supplies an actual original closed-fiber specialization of every total point. -/
theorem exists_completeClosedFiber_specialization (y : exactVeroneseProj K n h) :
    ∃ x : PolygonCyclicAtlas.scheme K n h, y ⤳ completeClosedFiberInclusion K n h x := by
  let _ := exactVeroneseProjToBase_isProper K n h
  obtain ⟨z, hyz, hz⟩ := (exactVeroneseProjToBase K n h).isClosedMap.specializingMap
    (a := y) (IsLocalRing.specializes_closedPoint ((exactVeroneseProjToBase K n h) y))
  have hr : z ∈ Set.range (completeClosedFiberInclusion K n h) := by
    rw [completeClosedFiber_range]
    exact hz
  obtain ⟨x, rfl⟩ := hr
  exact ⟨x, hyz⟩

end FLT.Mazur.PolygonInfinitesimalStages

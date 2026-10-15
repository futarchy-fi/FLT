/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCompleteClosedFiber

/-!
# Every actual complete-family point specializes into the original polygon

The original closed coefficient map has exactly the closed point as image.
Properness lifts specialization on the original local arithmetic base, and the
cartesian original closed fiber supplies its actual polygon preimage.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]

omit [IsNoetherianRing A] [IsDomain A] [IsAdicComplete (ideal A π) A] in
/-- The original coefficient reduction has precisely the arithmetic closed point as image. -/
theorem completeClosedBase_range :
    Set.range (completeClosedBase A) = {IsLocalRing.closedPoint A} := by
  have he : completeClosedBase A (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) =
      IsLocalRing.closedPoint A :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue A)
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    simpa only [Set.mem_singleton_iff,
      Subsingleton.elim z (IsLocalRing.closedPoint (IsLocalRing.ResidueField A))] using he
  · rintro rfl
    exact ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField A), he⟩

omit [IsAdicComplete (ideal A π) A] in
/-- The original polygon is exactly the inverse image of the original closed base point. -/
theorem completeClosedFiber_range :
    Set.range (completeClosedFiberInclusion A π hne hgen n h) =
      (exactVeroneseProjToBase A π n h hne hgen) ⁻¹' {IsLocalRing.closedPoint A} := by
  rw [← completeClosedFiberIso_fst]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (completeClosedFiberIso A π hne hgen n h).hom.surjective, Set.image_univ,
    Scheme.Pullback.range_fst, completeClosedBase_range]

/-- Properness supplies an actual original closed-fiber specialization of every total point. -/
theorem exists_completeClosedFiber_specialization (y : exactVeroneseProj A π n h hne hgen) :
    ∃ x : PolygonCyclicAtlas.scheme (IsLocalRing.ResidueField A) n h,
      y ⤳ completeClosedFiberInclusion A π hne hgen n h x := by
  let _ := exactVeroneseProjToBase_isProper A π n h hne hgen
  obtain ⟨z, hyz, hz⟩ := (exactVeroneseProjToBase A π n h hne hgen).isClosedMap.specializingMap
    (a := y) (IsLocalRing.specializes_closedPoint ((exactVeroneseProjToBase A π n h hne hgen) y))
  have hr : z ∈ Set.range (completeClosedFiberInclusion A π hne hgen n h) := by
    rw [completeClosedFiber_range]
    exact hz
  obtain ⟨x, rfl⟩ := hr
  exact ⟨x, hyz⟩

end FLT.Mazur.PolygonArithmeticStages

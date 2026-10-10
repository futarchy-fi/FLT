/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicBoundaryCharts

/-!
# The exact incidence image in the original conic

The intersection of the two original tangent neighborhoods is precisely
incidence away from zero, with the original conic functions retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R)
local notation "C₀" => ConicCoordinate a c
local notation "B" => ConicIncidenceOpen a c
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap C₀ B))

/-- Any point in both tangent neighborhoods lies on the original incidence boundary. -/
theorem conicTangent_intersection_subset_incidence :
    Set.range (conicFirstOpenImmersion a c) ∩
      Set.range (conicSecondOpenImmersion a c) ⊆ Set.range i := by
  rw [range_conicFirstOpenImmersion, range_conicSecondOpenImmersion,
    show Set.range i = (PrimeSpectrum.basicOpen (conicT a c) :
      Set (PrimeSpectrum C₀)) from PrimeSpectrum.localization_away_comap_range _ _]
  intro x hx ht
  have hr : conicV a c * (conicV a c + algebraMap R C₀ a) =
      algebraMap R C₀ c * conicT a c ^ 2 := sub_eq_zero.mp (conic_relation a c)
  have hm := x.asIdeal.mul_mem_left (algebraMap R C₀ c)
    (x.asIdeal.pow_mem_of_mem ht 2 (by decide))
  rw [← hr] at hm
  rcases x.isPrime.mem_or_mem hm with h | h
  · exact hx.2 h
  · exact hx.1 h

/-- For a unit constant, the entire incidence boundary is exactly that intersection. -/
theorem conicTangent_intersection_eq_incidence (ha : IsUnit a) (hc : IsUnit c) :
    Set.range (conicFirstOpenImmersion a c) ∩
      Set.range (conicSecondOpenImmersion a c) = Set.range i := by
  apply Set.Subset.antisymm (conicTangent_intersection_subset_incidence a c)
  rintro x ⟨y, rfl⟩
  constructor
  · refine ⟨((conicIncidenceFirstParameterMap a c ha hc) ≫
      (conicFirstParameterIso a c ha).inv) y, ?_⟩
    rw [← Scheme.Hom.comp_apply, Category.assoc, conicIncidenceFirstParameterMap_conic]
  · refine ⟨((conicIncidenceSecondParameterMap a c ha hc) ≫
      (conicSecondParameterIso a c ha).inv) y, ?_⟩
    rw [← Scheme.Hom.comp_apply, Category.assoc, conicIncidenceSecondParameterMap_conic]

end FLT.Mazur.WeierstrassModificationX

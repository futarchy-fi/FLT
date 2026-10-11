/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeGeometry
public import FLT.Mazur.WeierstrassModificationXFiberExteriorGeometry
public import FLT.Mazur.WeierstrassModificationXFiberConicOpen

/-!
# Both original components of the full node overlap

With an invertible conic constant the full tangent intersection is the union
of the punctured exterior and the complete conic incidence open. The two
pieces are disjoint, without discarding either component at equality depth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
universe u
variable {R : Type u} [CommRing R] (a c : R) (ha : IsUnit a)
local notation "F" => FiberCoordinate a c
local notation "t" => fiberT a c
local notation "v" => fiberV a c
local notation "q" => fiberConicFactor a c
local notation "e" => fiberExteriorSlopeChart a c
local notation "i" => PrincipalOpenTransport.inclusion t

/-- The entire exterior open lies in both original tangent charts at any constant. -/
theorem fullNodeOverlap_exterior_subset :
    Set.range e ⊆ Set.range (fullFirstNodeChart a c ha) ∩
      Set.range (fullSecondNodeChart a c ha) := by
  rw [fiberExteriorSlopeChart_range, range_fullFirstNodeChart, range_fullSecondNodeChart]
  intro x hq
  have ht : t ∈ x.asIdeal := by
    have h : t * q ∈ x.asIdeal := by
      rw [fiberConicFactor, fiber_relation]
      exact x.asIdeal.zero_mem
    exact (x.isPrime.mem_or_mem h).resolve_right hq
  have hct : algebraMap R F c * t ^ 2 ∈ x.asIdeal :=
    x.asIdeal.mul_mem_left _ (x.asIdeal.pow_mem_of_mem ht 2 (by decide))
  constructor
  · intro hv
    exact hq (x.asIdeal.sub_mem (x.asIdeal.mul_mem_left v hv) hct)
  · intro hv
    exact hq (x.asIdeal.sub_mem (x.asIdeal.mul_mem_right (v + algebraMap R F a) hv) hct)

/-- An invertible constant puts the full conic incidence open in both node charts. -/
theorem fullNodeOverlap_conic_subset (hc : IsUnit c) :
    Set.range i ⊆ Set.range (fullFirstNodeChart a c ha) ∩
      Set.range (fullSecondNodeChart a c ha) := by
  rw [show Set.range i = (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum F)) from
    PrimeSpectrum.localization_away_comap_range _ _,
    range_fullFirstNodeChart, range_fullSecondNodeChart]
  intro x ht
  have hq : q ∈ x.asIdeal := by
    have h : t * q ∈ x.asIdeal := by
      rw [fiberConicFactor, fiber_relation]
      exact x.asIdeal.zero_mem
    exact (x.isPrime.mem_or_mem h).resolve_left ht
  have hct : algebraMap R F c * t ^ 2 ∉ x.asIdeal := by
    intro h
    rcases x.isPrime.mem_or_mem h with h | h
    · exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hc.map (algebraMap R F)))
    · exact ht (x.isPrime.mem_of_pow_mem 2 h)
  constructor
  · intro hv
    apply hct
    have h := x.asIdeal.sub_mem (x.asIdeal.mul_mem_left v hv) hq
    simpa only [fiberConicFactor, sub_sub_cancel] using h
  · intro hv
    apply hct
    have h := x.asIdeal.sub_mem (x.asIdeal.mul_mem_right (v + algebraMap R F a) hv) hq
    simpa only [fiberConicFactor, sub_sub_cancel] using h

/-- Both full pieces, including the conic, exhaust the actual node intersection. -/
theorem fullNodeOverlap_range (hc : IsUnit c) :
    Set.range (fullFirstNodeChart a c ha) ∩ Set.range (fullSecondNodeChart a c ha) =
      Set.range e ∪ Set.range i := by
  apply Set.Subset.antisymm
  · rw [range_fullFirstNodeChart, range_fullSecondNodeChart, fiberExteriorSlopeChart_range,
      show Set.range i = (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum F)) from
        PrimeSpectrum.localization_away_comap_range _ _]
    intro x hx
    by_cases ht : t ∉ x.asIdeal
    · exact Or.inr ht
    · left
      intro hq
      have hct := x.asIdeal.mul_mem_left (algebraMap R F c)
        (x.asIdeal.pow_mem_of_mem (not_not.mp ht) 2 (by decide))
      have h := x.asIdeal.add_mem hq hct
      have hv : v * (v + algebraMap R F a) ∈ x.asIdeal := by
        simpa only [fiberConicFactor, sub_add_cancel] using h
      exact (x.isPrime.mem_or_mem hv).elim hx.2 hx.1
  · exact Set.union_subset (fullNodeOverlap_exterior_subset a c ha)
      (fullNodeOverlap_conic_subset a c ha hc)

/-- The two pieces of the original node overlap are disjoint. -/
theorem fullNodeOverlap_pieces_disjoint : Disjoint (Set.range e) (Set.range i) := by
  rw [fiberExteriorSlopeChart_range,
    show Set.range i = (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum F)) from
      PrimeSpectrum.localization_away_comap_range _ _]
  apply Set.disjoint_left.mpr
  intro x hq ht
  have h : t * q ∈ x.asIdeal := by
    rw [fiberConicFactor, fiber_relation]
    exact x.asIdeal.zero_mem
  exact (x.isPrime.mem_or_mem h).elim ht hq

end FLT.Mazur.WeierstrassModificationX

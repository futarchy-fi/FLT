/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeBadAffineCoverBoundaryUnits
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Boundary obstruction equations under scalar extension

The constructed obstruction equations extend along the boundary scalar map.
Their emptiness descends whenever the boundary spectra are covered, in particular
along a faithfully flat extension. All conclusions return to the original scalars.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeBadAffineCover
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R T S : Type} [CommRing R] [CommRing T] [CommRing S] {X : Scheme}
  [NoetherianSpace X] (s : R →+* Γ(X, ⊤)) (O : X.Opens) (κ : R →+* T) (φ : T →+* S)

/-- Formation of each boundary obstruction ideal commutes with arbitrary scalar extension. -/
theorem boundaryChartIdeal_comp (i : (badCover O).I₀) :
    boundaryChartIdeal s O (φ.comp κ) i = (boundaryChartIdeal s O κ i).map φ := by
  exact (Ideal.map_map _ _).symm

/-- The scalar extension induces an actual map on the obstruction coordinate rings. -/
def boundaryChartQuotientMap (i : (badCover O).I₀) :
    (T ⧸ boundaryChartIdeal s O κ i) →+* (S ⧸ boundaryChartIdeal s O (φ.comp κ) i) :=
  Ideal.quotientMap _ φ (by
    rw [boundaryChartIdeal_comp]
    exact Ideal.le_comap_map)

/-- The quotient map retains the original boundary scalar square. -/
theorem boundaryChartQuotientMap_comp_mk (i : (badCover O).I₀) :
    (boundaryChartQuotientMap s O κ φ i).comp
      (Ideal.Quotient.mk (boundaryChartIdeal s O κ i)) =
        (Ideal.Quotient.mk (boundaryChartIdeal s O (φ.comp κ) i)).comp φ :=
  Ideal.quotientMap_comp_mk _

/-- Membership in the obstruction after extension tests the unchanged contracted prime. -/
theorem boundaryChartObstruction_comp_mem_iff (i : (badCover O).I₀)
    (P : PrimeSpectrum S) :
    P ∈ Set.range (boundaryChartObstructionι s O (φ.comp κ) i) ↔
      PrimeSpectrum.comap φ P ∈ Set.range (boundaryChartObstructionι s O κ i) := by
  rw [mem_boundaryChartObstruction_range_iff, mem_boundaryChartObstruction_range_iff]
  rfl

/-- An empty obstruction remains empty after every boundary scalar extension. -/
theorem boundaryChart_empty_comp (i : (badCover O).I₀)
    (h : IsEmpty (boundaryChartObstruction s O κ i)) :
    IsEmpty (boundaryChartObstruction s O (φ.comp κ) i) := by
  apply (boundaryChartObstruction_empty_iff s O (φ.comp κ) i).mpr
  rw [boundaryChartIdeal_comp, (boundaryChartObstruction_empty_iff s O κ i).mp h,
    Ideal.map_top]

/-- A covering of boundary spectra reflects emptiness of each constructed obstruction. -/
theorem boundaryChart_empty_comp_iff
    (hφ : Function.Surjective (PrimeSpectrum.comap φ)) (i : (badCover O).I₀) :
    IsEmpty (boundaryChartObstruction s O (φ.comp κ) i) ↔
      IsEmpty (boundaryChartObstruction s O κ i) := by
  refine ⟨?_, boundaryChart_empty_comp s O κ φ i⟩
  intro h
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨P, hP⟩ := hφ (boundaryChartObstructionι s O κ i x)
  have hp : P ∈ Set.range (boundaryChartObstructionι s O (φ.comp κ) i) := by
    apply (boundaryChartObstruction_comp_mem_iff s O κ φ i P).mpr
    exact ⟨x, hP.symm⟩
  obtain ⟨y, _⟩ := hp
  exact h.false y

/-- Faithfully flat testing constructs a finite denominator equation over the original boundary. -/
theorem boundary_equation_of_faithfullyFlat [Algebra T S] [Module.FaithfullyFlat T S]
    (h : ∀ i, IsEmpty (boundaryChartObstruction s O ((algebraMap T S).comp κ) i)) :
    ∃ (n : ℕ) (a : Fin n → R) (b : Fin n → T),
      (∀ j, X.basicOpen (s (a j)) ≤ O) ∧ ∑ j, b j * κ (a j) = 1 := by
  apply (scalar_boundary_unit_ideal_iff_finite_equation s O κ).mp
  apply (scalar_boundary_cover_iff_unit_ideal s O κ).mp
  apply (all_scalar_safe_iff_boundaryChart_empty s O κ).mpr
  intro i
  exact (boundaryChart_empty_comp_iff s O κ (algebraMap T S)
    PrimeSpectrum.comap_surjective_of_faithfullyFlat i).mp (h i)

end FLT.Mazur.SchemeBadAffineCover

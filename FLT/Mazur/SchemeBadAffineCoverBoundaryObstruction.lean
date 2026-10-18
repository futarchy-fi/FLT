/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeBadAffineCoverReduced

/-!
# Closed boundary obstructions constructed from the actual bad charts

For each chart, first close its image in the original scalar spectrum, then
pull that closed image back to the original boundary. These explicit quotient
schemes detect accumulation, which the fiber of the bad chart itself need not detect.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeBadAffineCover
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R T : Type} [CommRing R] [CommRing T] {X : Scheme}
  [NoetherianSpace X] (s : R →+* Γ(X, ⊤)) (O : X.Opens) (κ : R →+* T)

/-- Equations of the chart's scalar image closure, extended to the original boundary. -/
def boundaryChartIdeal (i : (badCover O).I₀) : Ideal T :=
  (RingHom.ker (badChartScalar s O i)).map κ

/-- The boundary intersection with a closed bad-chart scalar image. -/
def boundaryChartObstruction (i : (badCover O).I₀) : Scheme :=
  Spec (.of (T ⧸ boundaryChartIdeal s O κ i))

/-- The obstruction embeds in the unchanged boundary scalar spectrum. -/
def boundaryChartObstructionι (i : (badCover O).I₀) :
    boundaryChartObstruction s O κ i ⟶ Spec (.of T) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (boundaryChartIdeal s O κ i)))

/-- Closing the actual bad-chart scalar image gives precisely its kernel equations. -/
theorem badChart_scalar_image_closure (i : (badCover O).I₀) :
    closure (Set.range (scalarMorphism (badChartScalar s O i))) =
      PrimeSpectrum.zeroLocus (RingHom.ker (badChartScalar s O i) : Set R) := by
  rw [scalarMorphism_range_eq_comap, PrimeSpectrum.closure_range_comap]

/-- The constructed closed obstruction has exactly the specified boundary equations. -/
theorem boundaryChartObstruction_range (i : (badCover O).I₀) :
    Set.range (boundaryChartObstructionι s O κ i) =
      PrimeSpectrum.zeroLocus (boundaryChartIdeal s O κ i : Set T) := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (boundaryChartIdeal s O κ i))) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker]

/-- A boundary prime lies on the obstruction exactly when it contains the chart kernel. -/
theorem mem_boundaryChartObstruction_range_iff (i : (badCover O).I₀)
    (P : PrimeSpectrum T) :
    P ∈ Set.range (boundaryChartObstructionι s O κ i) ↔
      RingHom.ker (badChartScalar s O i) ≤ P.asIdeal.comap κ := by
  rw [boundaryChartObstruction_range]
  change boundaryChartIdeal s O κ i ≤ P.asIdeal ↔ _
  exact Ideal.map_le_iff_le_comap

/-- Avoiding one obstruction constructs an exact scalar separator for that chart. -/
theorem not_mem_boundaryChartObstruction_range_iff (i : (badCover O).I₀)
    (P : PrimeSpectrum T) :
    P ∉ Set.range (boundaryChartObstructionι s O κ i) ↔
      ∃ r : R, κ r ∉ P.asIdeal ∧ badChartScalar s O i r = 0 := by
  rw [mem_boundaryChartObstruction_range_iff]
  constructor
  · intro h
    obtain ⟨r, hz, hr⟩ := IsConcreteLE.not_le_iff_exists.mp h
    exact ⟨r, hr, hz⟩
  · rintro ⟨r, hr, hz⟩ h
    exact hr (h hz)

/-- Original-prime safety is equivalent to avoiding this finite family of closed obstructions. -/
theorem scalar_safe_iff_boundaryChart_obstructions (P : PrimeSpectrum T) :
    PrimeSpectrum.comap κ P ∈ scalarNeighborhoodLocus s O ↔
      ∀ i, P ∉ Set.range (boundaryChartObstructionι s O κ i) := by
  constructor
  · intro h i
    obtain ⟨r, hr, hz⟩ := (mem_scalarNeighborhoodLocus_iff_badChart_zero O s _).mp h
    exact (not_mem_boundaryChartObstruction_range_iff s O κ i P).mpr ⟨r, hr, hz i⟩
  · intro h
    have hs := fun i ↦ (not_mem_boundaryChartObstruction_range_iff s O κ i P).mp (h i)
    choose a ha hz using hs
    obtain ⟨hp, hO⟩ := badChart_kernel_product s O (PrimeSpectrum.comap κ P) a
      (fun i ↦ ⟨ha i, hz i⟩)
    exact (mem_scalarNeighborhoodLocus_iff s O _).mpr ⟨_, hp, hO⟩

/-- Every failure of safety is witnessed by a point of a constructed closed boundary scheme. -/
theorem not_scalar_safe_iff_boundaryChart_point (P : PrimeSpectrum T) :
    PrimeSpectrum.comap κ P ∉ scalarNeighborhoodLocus s O ↔
      ∃ (i : (badCover O).I₀) (x : boundaryChartObstruction s O κ i),
        boundaryChartObstructionι s O κ i x = P := by
  rw [scalar_safe_iff_boundaryChart_obstructions]
  push Not
  rfl

end FLT.Mazur.SchemeBadAffineCover

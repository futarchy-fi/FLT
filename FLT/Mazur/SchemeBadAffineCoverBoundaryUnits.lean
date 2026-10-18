/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeBadAffineCoverBoundaryObstruction
public import FLT.Mazur.SchemeScalarBoundaryUnitCover

/-!
# Finite equations for the closed bad-chart boundary obstructions

Emptiness of each explicitly constructed obstruction is equivalent to a finite
unit equation using scalars killed on that chart. The finite atlas combines
these separate equations into full original denominators. No integrality or
Noetherian hypothesis on either scalar ring is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeBadAffineCover
open SchemeScalarPrincipalNeighborhood SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R T : Type} [CommRing R] [CommRing T] {X : Scheme}
  [NoetherianSpace X] (s : R →+* Γ(X, ⊤)) (O : X.Opens) (κ : R →+* T)

/-- The closed boundary obstruction is empty exactly when its defining ideal is the unit ideal. -/
theorem boundaryChartObstruction_empty_iff (i : (badCover O).I₀) :
    IsEmpty (boundaryChartObstruction s O κ i) ↔ boundaryChartIdeal s O κ i = ⊤ := by
  change IsEmpty (PrimeSpectrum (T ⧸ boundaryChartIdeal s O κ i)) ↔ _
  rw [PrimeSpectrum.isEmpty_iff_subsingleton, Ideal.Quotient.subsingleton_iff]

/-- The entire original boundary is safe exactly when every constructed obstruction is empty. -/
theorem all_scalar_safe_iff_boundaryChart_empty :
    (∀ P : PrimeSpectrum T, PrimeSpectrum.comap κ P ∈ scalarNeighborhoodLocus s O) ↔
      ∀ i, IsEmpty (boundaryChartObstruction s O κ i) := by
  constructor
  · intro h i
    exact ⟨fun x ↦ ((scalar_safe_iff_boundaryChart_obstructions s O κ _).mp
      (h (boundaryChartObstructionι s O κ i x))) i ⟨x, rfl⟩⟩
  · intro h P
    apply (scalar_safe_iff_boundaryChart_obstructions s O κ P).mpr
    rintro i ⟨x, _⟩
    exact (h i).false x

/-- The single original denominator ideal is a unit on the boundary iff each chart kernel is. -/
theorem boundary_denominator_unit_iff_chart_units :
    (denominatorIdeal s O).map κ = ⊤ ↔ ∀ i, boundaryChartIdeal s O κ i = ⊤ := by
  rw [← scalar_boundary_cover_iff_unit_ideal, all_scalar_safe_iff_boundaryChart_empty]
  exact forall_congr' fun i ↦ boundaryChartObstruction_empty_iff s O κ i

/-- An individual chart obstruction is empty iff finitely many exact kernel scalars generate one. -/
theorem boundaryChart_empty_iff_finite_equation (i : (badCover O).I₀) :
    IsEmpty (boundaryChartObstruction s O κ i) ↔
      ∃ (n : ℕ) (a : Fin n → R) (b : Fin n → T),
        (∀ j, badChartScalar s O i (a j) = 0) ∧ ∑ j, b j * κ (a j) = 1 := by
  classical
  rw [boundaryChartObstruction_empty_iff]
  constructor
  · intro h
    have hone : (1 : T) ∈ Submodule.span T
        (κ '' (RingHom.ker (badChartScalar s O i) : Set R)) := by
      change (1 : T) ∈ boundaryChartIdeal s O κ i
      rw [h]
      trivial
    obtain ⟨n, b, g, hg⟩ := Submodule.mem_span_set'.mp hone
    choose a ha hκ using fun j ↦ (g j).property
    refine ⟨n, a, b, ha, ?_⟩
    calc
      ∑ j, b j * κ (a j) = ∑ j, b j * (g j).val := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hκ j]
      _ = 1 := hg
  · rintro ⟨n, a, b, ha, hab⟩
    rw [Ideal.eq_top_iff_one, ← hab]
    exact sum_mem fun j _ ↦ (boundaryChartIdeal s O κ i).mul_mem_left (b j)
      (Ideal.mem_map_of_mem κ (ha j))

/-- Separate chart equations construct one finite equation of full original denominators. -/
theorem exists_boundary_denominator_equation_of_chart_equations
    (h : ∀ i, ∃ (n : ℕ) (a : Fin n → R) (b : Fin n → T),
      (∀ j, badChartScalar s O i (a j) = 0) ∧ ∑ j, b j * κ (a j) = 1) :
    ∃ (n : ℕ) (a : Fin n → R) (b : Fin n → T),
      (∀ j, X.basicOpen (s (a j)) ≤ O) ∧ ∑ j, b j * κ (a j) = 1 := by
  apply (scalar_boundary_unit_ideal_iff_finite_equation s O κ).mp
  apply (scalar_boundary_cover_iff_unit_ideal s O κ).mp
  apply (all_scalar_safe_iff_boundaryChart_empty s O κ).mpr
  intro i
  exact (boundaryChart_empty_iff_finite_equation s O κ i).mpr (h i)

end FLT.Mazur.SchemeBadAffineCover

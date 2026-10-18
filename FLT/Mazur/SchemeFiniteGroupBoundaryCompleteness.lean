/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupFiniteFiberTests
public import FLT.Mazur.AffineScalarBoundaryNilpotence

/-!
# Universal whole-fiber containment as finite boundary nilpotence

Pull the fixed invariant support functions to the full original scalar boundary
product. Their nilpotence is equivalent to containment of every original scalar
fiber in the stable closed locus. No radical replacement of that product occurs.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeFiniteGroupQuotient
open SchemeScalarPrincipalNeighborhood AffineScalarBoundaryNilpotence
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct boundaryCoordinate
variable {G : Type} [Group G] [Finite G] {X : Scheme} [IsAffine X]
  [NoetherianSpace X] (ρ : G →* Aut X) (Z : Set X) (hZ : IsClosed Z)
  (hstable : ∀ (g : G) (x : X), x ∈ Z → (ρ g).hom x ∈ Z)
  {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* invariantCoordinates ρ) (κ : R →+* T)
local notation "s₀" => invariantScalarCoordinates ρ s

include hstable in
/-- All unchanged boundary scalar fibers are tested by finitely many actual nilpotent sections. -/
theorem all_scalar_fibers_subset_iff_boundary_nilpotent :
    (∀ (P : PrimeSpectrum T) (x : X),
      scalarMorphism s₀ x = PrimeSpectrum.comap κ P → x ∈ Z) ↔
      ∀ b ∈ closedOrbitTests ρ Z hZ, IsNilpotent (boundaryCoordinate s κ b) := by
  simp_rw [boundaryCoordinate_nilpotent_iff]
  constructor
  · intro h b hb Q P hc
    have hQ := (scalar_fiber_subset_iff ρ Z hZ hstable s (PrimeSpectrum.comap κ P)).mp
      (h P) Q hc
    exact (mem_closedOrbitImage_iff_tests ρ Z hZ Q).mp hQ b hb
  · intro h P
    apply (scalar_fiber_subset_iff ρ Z hZ hstable s (PrimeSpectrum.comap κ P)).mpr
    intro Q hc
    exact (mem_closedOrbitImage_iff_tests ρ Z hZ Q).mpr (fun b hb ↦ h b hb Q P hc)

include hstable in
/-- Non-nilpotence constructs an incomplete original chart point over an actual boundary prime. -/
theorem exists_boundary_fiber_point_of_not_nilpotent
    (b : invariantCoordinates ρ) (hb : b ∈ closedOrbitTests ρ Z hZ)
    (hn : ¬ IsNilpotent (boundaryCoordinate s κ b)) :
    ∃ (P : PrimeSpectrum T) (x : X),
      scalarMorphism s₀ x = PrimeSpectrum.comap κ P ∧ x ∉ Z := by
  by_contra h
  push Not at h
  exact hn ((all_scalar_fibers_subset_iff_boundary_nilpotent ρ Z hZ hstable s κ).mp h b hb)

include hstable in
/-- Universal fiber containment has one nilpotence exponent for all fixed boundary functions. -/
theorem all_scalar_fibers_subset_iff_boundary_power :
    (∀ (P : PrimeSpectrum T) (x : X),
      scalarMorphism s₀ x = PrimeSpectrum.comap κ P → x ∈ Z) ↔
      ∃ n : ℕ, ∀ b ∈ closedOrbitTests ρ Z hZ, boundaryCoordinate s κ b ^ n = 0 := by
  classical
  rw [all_scalar_fibers_subset_iff_boundary_nilpotent ρ Z hZ hstable s κ]
  constructor
  · intro h
    choose n hn using (fun b : closedOrbitTests ρ Z hZ ↦ h b.val b.property)
    refine ⟨Finset.univ.sup n, fun b hb ↦ ?_⟩
    exact pow_eq_zero_of_le (Finset.le_sup (Finset.mem_univ (⟨b, hb⟩ :
      closedOrbitTests ρ Z hZ))) (hn ⟨b, hb⟩)
  · rintro ⟨n, h⟩ b hb
    exact ⟨n, h b hb⟩

end FLT.Mazur.SchemeFiniteGroupQuotient

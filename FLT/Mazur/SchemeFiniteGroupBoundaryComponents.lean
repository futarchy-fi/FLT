/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryComponentEquations
public import FLT.Mazur.SchemeFiniteGroupBoundaryCompleteness

/-!
# Actual original chart lifts of minimal boundary components

Every minimal component of the full scalar boundary product supplies an
original chart point and an unchanged boundary prime. Stable closed containment
can be checked on one such lift per component; this is stronger than checking
one orbit over an arbitrary scalar prime.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeFiniteGroupQuotient
open SchemeScalarPrincipalNeighborhood AffineScalarBoundaryNilpotence
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryCoordinate boundaryComponentPoint
variable {G : Type} [Group G] [Finite G] {X : Scheme} [IsAffine X]
  [NoetherianSpace X] (ρ : G →* Aut X) (Z : Set X) (hZ : IsClosed Z)
  (hstable : ∀ (g : G) (x : X), x ∈ Z → (ρ g).hom x ∈ Z)
  {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* invariantCoordinates ρ) (κ : R →+* T)
set_option quotPrecheck false
local notation "C" => Γ(boundaryProduct s κ, ⊤)
local notation "s₀" => invariantScalarCoordinates ρ s

/-- The boundary prime paired with the generic point of an actual minimal product component. -/
def componentBoundaryPrime (Q : minimalPrimes C) : PrimeSpectrum T :=
  pullback.snd (Spec.map (CommRingCat.ofHom s)) (Spec.map (CommRingCat.ofHom κ))
    (boundaryComponentPoint s κ Q)

omit [NoetherianSpace X] in
/-- Every component has an original chart lift at its unchanged original boundary prime. -/
theorem exists_component_chart_lift (Q : minimalPrimes C) :
    ∃ x : X, quotientMap ρ x = boundaryProjection s κ (boundaryComponentPoint s κ Q) ∧
      scalarMorphism s₀ x = PrimeSpectrum.comap κ (componentBoundaryPrime ρ s κ Q) := by
  obtain ⟨x, hx⟩ := (quotientMap ρ).surjective
    (boundaryProjection s κ (boundaryComponentPoint s κ Q))
  refine ⟨x, hx, ?_⟩
  rw [scalarMorphism_through_quotient]
  change PrimeSpectrum.comap s (quotientMap ρ x) = _
  rw [hx]
  exact congrArg (fun f ↦ f (boundaryComponentPoint s κ Q))
    (pullback.condition (f := Spec.map (CommRingCat.ofHom s))
      (g := Spec.map (CommRingCat.ofHom κ)))

/-- The fixed equations on a domain component test its entire original chart orbit. -/
theorem component_equations_iff_closed_image (Q : minimalPrimes C) :
    (∀ b ∈ closedOrbitTests ρ Z hZ,
      Ideal.Quotient.mk Q.val (boundaryCoordinate s κ b) = 0) ↔
      boundaryProjection s κ (boundaryComponentPoint s κ Q) ∈ closedOrbitImage ρ Z hZ := by
  simp_rw [boundaryComponent_equation_iff]
  exact (mem_closedOrbitImage_iff_tests ρ Z hZ _).symm

include hZ hstable in
/-- One closed-locus lift per minimal component proves containment of every scalar fiber. -/
theorem all_scalar_fibers_subset_iff_component_lifts :
    (∀ (P : PrimeSpectrum T) (x : X),
      scalarMorphism s₀ x = PrimeSpectrum.comap κ P → x ∈ Z) ↔
      ∀ Q : minimalPrimes C, ∃ x : X,
        quotientMap ρ x = boundaryProjection s κ (boundaryComponentPoint s κ Q) ∧ x ∈ Z := by
  rw [all_scalar_fibers_subset_iff_boundary_nilpotent ρ Z hZ hstable s κ]
  simp_rw [boundaryCoordinate_nilpotent_iff_components]
  constructor
  · intro h Q
    have hQ := (component_equations_iff_closed_image ρ Z hZ s κ Q).mp
      (fun b hb ↦ h b hb Q)
    obtain ⟨x, hx, he⟩ := hQ
    exact ⟨x, he, hx⟩
  · intro h b hb Q
    obtain ⟨x, he, hx⟩ := h Q
    exact (component_equations_iff_closed_image ρ Z hZ s κ Q).mpr ⟨x, hx, he⟩ b hb

/-- A failed fixed equation has a bad original lift over an actual minimal product component. -/
theorem exists_bad_component_chart_lift (b : invariantCoordinates ρ)
    (hb : b ∈ closedOrbitTests ρ Z hZ) (hn : ¬ IsNilpotent (boundaryCoordinate s κ b)) :
    ∃ (Q : minimalPrimes C) (x : X),
      quotientMap ρ x = boundaryProjection s κ (boundaryComponentPoint s κ Q) ∧
      scalarMorphism s₀ x = PrimeSpectrum.comap κ (componentBoundaryPrime ρ s κ Q) ∧
      x ∉ Z ∧ Ideal.Quotient.mk Q.val (boundaryCoordinate s κ b) ≠ 0 := by
  obtain ⟨Q, hQ⟩ := exists_boundary_component_nonzero s κ b hn
  obtain ⟨x, hx, hs⟩ := exists_component_chart_lift ρ s κ Q
  refine ⟨Q, x, hx, hs, ?_, hQ⟩
  intro hz
  exact hQ ((component_equations_iff_closed_image ρ Z hZ s κ Q).mpr ⟨x, hz, hx⟩ b hb)

end FLT.Mazur.SchemeFiniteGroupQuotient

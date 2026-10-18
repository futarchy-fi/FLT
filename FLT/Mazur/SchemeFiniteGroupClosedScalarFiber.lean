/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupQuotientOrbits
public import FLT.Mazur.SchemeOriginalScalarOpenCorrections

/-!
# Whole scalar fibers of stable closed loci

A finite group quotient carries an actual closed image of every stable closed
locus. Its inverse image is exactly the original locus. Whole fibers over a
smaller scalar ring are tested on every invariant prime over that scalar prime.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] [Finite G] {X : Scheme} [IsAffine X]
  (ρ : G →* Aut X) (Z : Set X) (hZ : IsClosed Z)
  (hstable : ∀ (g : G) (x : X), x ∈ Z → (ρ g).hom x ∈ Z)

/-- The actual closed set of invariant primes represented by points in the original locus. -/
def closedOrbitImage : TopologicalSpace.Closeds (quotient ρ) :=
  ⟨quotientMap ρ '' Z, (quotientMap ρ).isClosedMap Z hZ⟩

include hstable in
/-- The quotient forgets no points of the stable closed locus. -/
theorem closedOrbitImage_preimage :
    quotientMap ρ ⁻¹' (closedOrbitImage ρ Z hZ : Set _) = Z :=
  quotientMap_saturated ρ Z hstable

include hstable in
/-- A single orbit prime belongs to the closed image exactly when its entire fiber does. -/
theorem mem_closedOrbitImage_iff_fiber (Q : quotient ρ) :
    Q ∈ closedOrbitImage ρ Z hZ ↔ ∀ x : X, quotientMap ρ x = Q → x ∈ Z := by
  constructor
  · intro h x hx
    have : x ∈ quotientMap ρ ⁻¹' (closedOrbitImage ρ Z hZ : Set _) := by
      change quotientMap ρ x ∈ closedOrbitImage ρ Z hZ
      rwa [hx]
    rwa [closedOrbitImage_preimage ρ Z hZ hstable] at this
  · intro h
    obtain ⟨x, rfl⟩ := (quotientMap ρ).surjective Q
    exact ⟨x, h x rfl, rfl⟩

variable {R : Type} [CommRing R] (s : R →+* invariantCoordinates ρ)
local notation "s₀" => invariantScalarCoordinates ρ s

omit [Finite G] [IsAffine X] in
/-- The original scalar map factors through the constructed invariant quotient. -/
theorem scalarMorphism_through_quotient :
    scalarMorphism s₀ = quotientMap ρ ≫ Spec.map (CommRingCat.ofHom s) := by
  let _ := SchemeCoordinateAction.coordinateAction ρ
  change X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom s₀) =
    (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (FiniteGroupQuotient.inclusion G Γ(X, ⊤)))) ≫ _
  rw [Category.assoc, ← Spec.map_comp]
  rfl

include hstable in
/-- All original scalar points lie in the locus iff every invariant prime above them does. -/
theorem scalar_fiber_subset_iff (P : PrimeSpectrum R) :
    (∀ x : X, scalarMorphism s₀ x = P → x ∈ Z) ↔
      ∀ Q : PrimeSpectrum (invariantCoordinates ρ), PrimeSpectrum.comap s Q = P →
        Q ∈ closedOrbitImage ρ Z hZ := by
  rw [scalarMorphism_through_quotient]
  constructor
  · intro h Q hQ
    apply (mem_closedOrbitImage_iff_fiber ρ Z hZ hstable Q).mpr
    intro x hx
    exact h x (by change PrimeSpectrum.comap s (quotientMap ρ x) = P; rwa [hx])
  · intro h x hx
    apply (mem_closedOrbitImage_iff_fiber ρ Z hZ hstable (quotientMap ρ x)).mp
      (h (quotientMap ρ x) hx) x rfl

end FLT.Mazur.SchemeFiniteGroupQuotient

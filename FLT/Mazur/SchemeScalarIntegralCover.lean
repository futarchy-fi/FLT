/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarAvoidanceCover
public import FLT.Mazur.SchemeScalarPrincipalNeighborhoodFamily
public import FLT.Mazur.SchemeEffectiveEpiSections

/-!
# Original scalar neighborhoods from integral covering coordinates

An affine surjective source integral over the original scalar ring makes the
original scalar morphism closed, even when the target is not affine. Fiber
containment can then be checked on that source. For scheme epimorphisms,
integrality also descends to the full target coordinate ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X Y : Scheme}
  (s : R →+* Γ(X, ⊤)) (g : Y ⟶ X)

/-- Integral pullback coordinates descend through any scheme epimorphism. -/
theorem scalarCoordinates_isIntegral_of_cover [Epi g]
    (hs : (g.appTop.hom.comp s).IsIntegral) : s.IsIntegral := by
  intro x
  exact RingHom.IsIntegralElem.of_map
    (SchemeEffectiveEpiSections.appTop_injective g) (hs (g.appTop x))

variable [IsAffine Y] [Surjective g]

/-- Integral affine covering coordinates make the original target scalar map closed. -/
theorem scalarMorphism_isClosedMap_of_cover
    (hs : (g.appTop.hom.comp s).IsIntegral) :
    IsClosedMap (scalarMorphism s) := by
  intro C hC
  have hclosed := scalarMorphism_isClosedMap (g.appTop.hom.comp s) hs
    (g ⁻¹' C) (hC.preimage g.continuous)
  have he : scalarMorphism (g.appTop.hom.comp s) '' (g ⁻¹' C) =
      scalarMorphism s '' C := by
    rw [scalarMorphism_comp]
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨g y, hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, rfl⟩ := g.surjective x
      exact ⟨y, hx, rfl⟩
  rwa [he] at hclosed

/-- A whole fiber on an integral cover constructs an outside-prime original denominator. -/
theorem exists_scalar_of_integral_cover_fiber
    (hs : (g.appTop.hom.comp s).IsIntegral) (O : X.Opens) (P : PrimeSpectrum R)
    (hP : ∀ y : Y, scalarMorphism (g.appTop.hom.comp s) y = P → g y ∈ O) :
    ∃ r : R, r ∉ P.asIdeal ∧ X.basicOpen (s r) ≤ O :=
  exists_scalar_of_closed_fiber s O P (scalarMorphism_isClosedMap_of_cover s g hs)
    ((scalarFiber_cover_iff s g O P).mp hP)

/-- Integral covering fibers prove noncontainment of the actual original avoidance ideal. -/
theorem scalarAvoidanceIdeal_not_le_of_integral_cover
    (hs : (g.appTop.hom.comp s).IsIntegral) (O : X.Opens) (P : PrimeSpectrum R)
    (hP : ∀ y : Y, scalarMorphism (g.appTop.hom.comp s) y = P → g y ∈ O) :
    ¬ scalarAvoidanceIdeal s O ≤ P.asIdeal := by
  obtain ⟨r, hr, hO⟩ := exists_scalar_of_integral_cover_fiber s g hs O P hP
  intro h
  exact hr (h ((mem_scalarAvoidanceIdeal_iff s O r).mpr hO))

end FLT.Mazur.SchemeScalarPrincipalNeighborhood

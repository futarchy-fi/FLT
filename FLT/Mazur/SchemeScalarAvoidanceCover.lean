/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarAvoidanceIdeal
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Computing original scalar avoidance on surjective covers

The bad image and its original denominator ideal can be computed on any
surjective scheme cover. This keeps the original scalar ring and its prime
unchanged and requires neither complete frames nor reduced schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X Y : Scheme}
  (s : R →+* Γ(X, ⊤)) (g : Y ⟶ X)

/-- Pulling back scalar coordinates composes the original scalar morphism. -/
@[reassoc] theorem scalarMorphism_comp :
    scalarMorphism (g.appTop.hom.comp s) = g ≫ scalarMorphism s := by
  unfold scalarMorphism
  rw [Scheme.toSpecΓ_naturality_assoc]
  rw [← Spec.map_comp]
  rfl

variable [Surjective g]

/-- A surjective cover gives exactly the same bad image in the original scalar spectrum. -/
theorem scalar_badImage_cover (O : X.Opens) :
    scalarMorphism (g.appTop.hom.comp s) '' ((g ⁻¹ᵁ O : Y.Opens) : Set Y)ᶜ =
      scalarMorphism s '' (O : Set X)ᶜ := by
  rw [scalarMorphism_comp]
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g y, hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, rfl⟩ := g.surjective x
    exact ⟨y, hx, rfl⟩

/-- Original denominator ideals are unchanged by computation on a surjective cover. -/
theorem scalarAvoidanceIdeal_cover (O : X.Opens) :
    scalarAvoidanceIdeal (g.appTop.hom.comp s) (g ⁻¹ᵁ O) =
      scalarAvoidanceIdeal s O := by
  unfold scalarAvoidanceIdeal
  rw [scalar_badImage_cover]

/-- Safe original prime loci are unchanged by computation on a surjective cover. -/
theorem scalarNeighborhoodLocus_cover (O : X.Opens) :
    scalarNeighborhoodLocus (g.appTop.hom.comp s) (g ⁻¹ᵁ O) =
      scalarNeighborhoodLocus s O := by
  apply SetLike.coe_injective
  change (closure _)ᶜ = (closure _)ᶜ
  rw [scalar_badImage_cover]

/-- Whole-fiber containment can be tested on the actual surjective source. -/
theorem scalarFiber_cover_iff (O : X.Opens) (P : PrimeSpectrum R) :
    (∀ y : Y, scalarMorphism (g.appTop.hom.comp s) y = P → g y ∈ O) ↔
      ∀ x : X, scalarMorphism s x = P → x ∈ O := by
  rw [scalarMorphism_comp]
  constructor
  · intro h x hx
    obtain ⟨y, rfl⟩ := g.surjective x
    exact h y hx
  · intro h y hy
    exact h (g y) hy

end FLT.Mazur.SchemeScalarPrincipalNeighborhood

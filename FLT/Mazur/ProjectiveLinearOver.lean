/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLinearIsomorphism

/-!
# Linear projective transitions over the coefficient scheme

Linear coordinate changes preserve the coefficient projection. They therefore
provide isomorphisms over the affine base for gluing local projective bundles.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.ProjectiveSpace
variable {R : Type u} [CommRing R] {ι κ : Type u}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every invertible linear coordinate change respects the actual coefficient projection. -/
@[reassoc]
lemma linearIso_baseProjection (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) :
    (linearIso e).hom ≫ baseProjection R κ = baseProjection R ι := by
  apply (Proj.mapAffineOpenCover (linearGradedMap e.symm.toLinearMap)
    (linearGradedMap_irrelevant e.symm)).openCover.hom_ext
  intro s
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f]
  change Proj.awayι _ _ _ _ ≫ Proj.map _ _ ≫
    (Proj.toSpecZero _ ≫ Spec.map _) = Proj.awayι _ _ _ _ ≫ (Proj.toSpecZero _ ≫ _)
  rw [Proj.awayι_comp_map_assoc _ _ _ _ s.2.2, Proj.awayι_toSpecZero_assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  apply val_injective
  simp [constantsToZero, fromZeroRingHom, Away.map, HomogeneousLocalization.map_mk,
    linearGradedMap, linearSubstitution]

/-- A linear change of coordinates as an isomorphism in the category over Spec R. -/
def linearOverIso (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) :
    Over.mk (baseProjection R ι) ≅ Over.mk (baseProjection R κ) :=
  Over.isoMk (linearIso e) (linearIso_baseProjection e)

/-- Forgetting the base retains the constructed projective isomorphism. -/
lemma linearOverIso_hom_left (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) :
    (linearOverIso e).hom.left = (linearIso e).hom := rfl

end FLT.Mazur.ProjectiveSpace

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLinearSubstitution

/-!
# Projective isomorphisms from linear coordinate changes

An invertible linear change preserves the irrelevant ideal and therefore
induces an actual isomorphism of polynomial Proj schemes. Identity, inverse,
and cocycle laws follow from the corresponding graded substitutions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.ProjectiveSpace
variable {R : Type u} [CommRing R] {ι κ ν : Type u}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Inverse linear changes cancel on the entire homogeneous coordinate ring. -/
lemma linearGradedMap_inverse (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) :
    (linearGradedMap e.symm.toLinearMap).comp (linearGradedMap e.toLinearMap) =
      .id (grading R ι) := by
  rw [linearGradedMap_comp, LinearEquiv.symm_comp, linearGradedMap_id]

/-- An invertible linear substitution carries the irrelevant ideal onto the irrelevant ideal. -/
lemma linearGradedMap_irrelevant (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) :
    HomogeneousIdeal.irrelevant (grading R κ) ≤
      (HomogeneousIdeal.irrelevant (grading R ι)).map (linearGradedMap e.toLinearMap) := by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro n hn p hp
  have h := HomogeneousIdeal.mem_irrelevant_of_mem (grading R ι) hn
    ((linearGradedMap e.symm.toLinearMap).map_mem hp)
  have hm := Ideal.mem_map_of_mem (linearGradedMap e.toLinearMap).toRingHom h
  have he := DFunLike.congr_fun (linearGradedMap_inverse e.symm) p
  change (linearGradedMap e.toLinearMap)
    ((linearGradedMap e.symm.toLinearMap) p) = p at he
  change (linearGradedMap e.toLinearMap)
    ((linearGradedMap e.symm.toLinearMap) p) ∈ _ at hm
  rw [he] at hm
  exact hm

/-- An actual projective-space isomorphism induced by an invertible linear coordinate change. -/
def linearIso (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) : space R ι ≅ space R κ where
  hom := Proj.map (linearGradedMap e.symm.toLinearMap) (linearGradedMap_irrelevant e.symm)
  inv := Proj.map (linearGradedMap e.toLinearMap) (linearGradedMap_irrelevant e)
  hom_inv_id := by
    rw [← Proj.map_comp]
    simpa only [linearGradedMap_inverse] using Proj.map_id (𝒜 := grading R ι)
  inv_hom_id := by
    rw [← Proj.map_comp]
    have h := linearGradedMap_inverse e.symm
    simp only [LinearEquiv.symm_symm] at h
    simpa only [h] using Proj.map_id (𝒜 := grading R κ)

/-- The inverse coordinate change induces the inverse projective isomorphism. -/
lemma linearIso_symm (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) :
    (linearIso e).symm = linearIso e.symm := rfl

/-- Identity coordinates induce the identity projective map. -/
lemma linearIso_refl : linearIso (LinearEquiv.refl R (ι →₀ R)) = Iso.refl _ := by
  apply Iso.ext
  change Proj.map (linearGradedMap (LinearMap.id : (ι →₀ R) →ₗ[R] _)) _ = 𝟙 _
  simpa only [linearGradedMap_id] using Proj.map_id (𝒜 := grading R ι)

/-- Projective coordinate changes satisfy the same cocycle law as their linear changes. -/
lemma linearIso_trans (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R))
    (d : (κ →₀ R) ≃ₗ[R] (ν →₀ R)) :
    linearIso e ≪≫ linearIso d = linearIso (e.trans d) := by
  apply Iso.ext
  change Proj.map _ _ ≫ Proj.map _ _ = Proj.map _ _
  rw [← Proj.map_comp]
  congr 1
  exact linearGradedMap_comp d.symm.toLinearMap e.symm.toLinearMap

end FLT.Mazur.ProjectiveSpace

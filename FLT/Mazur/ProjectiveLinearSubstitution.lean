/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveSpaceReindex

/-!
# Linear changes of homogeneous coordinates

Linear maps of free modules extend to graded polynomial homomorphisms.
The extension preserves identities and composition, so a change of basis
induces an invertible graded change of homogeneous coordinates.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.ProjectiveSpace
variable {R : Type u} [CommRing R] {ι κ ν : Type u}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A vector of coefficients determines its homogeneous linear polynomial. -/
def linearForm : (ι →₀ R) →ₗ[R] MvPolynomial ι R := Finsupp.linearCombination R X

@[simp]
lemma linearForm_single (i : ι) (r : R) :
    linearForm (Finsupp.single i r) = r • X i := Finsupp.linearCombination_single _ _ _

/-- Every linear form is homogeneous of degree one, including the zero form. -/
lemma linearForm_homogeneous (v : ι →₀ R) : (linearForm v).IsHomogeneous 1 := by
  classical
  change (Finsupp.linearCombination R X v).IsHomogeneous 1
  rw [Finsupp.linearCombination_apply]
  exact (homogeneousSubmodule ι R 1).sum_mem fun i _ ↦
    (homogeneousSubmodule ι R 1).smul_mem _ (isHomogeneous_X R i)

/-- Substitute the columns of a linear map for the homogeneous variables. -/
def linearSubstitution (f : (ι →₀ R) →ₗ[R] (κ →₀ R)) :
    MvPolynomial ι R →ₐ[R] MvPolynomial κ R :=
  aeval fun i ↦ linearForm (f (Finsupp.single i 1))

@[simp]
lemma linearSubstitution_X (f : (ι →₀ R) →ₗ[R] (κ →₀ R)) (i : ι) :
    linearSubstitution f (X i) = linearForm (f (Finsupp.single i 1)) := aeval_X _ _

/-- Substitution acts on all linear forms by the original linear map. -/
lemma linearSubstitution_linearForm (f : (ι →₀ R) →ₗ[R] (κ →₀ R)) (v : ι →₀ R) :
    linearSubstitution f (linearForm v) = linearForm (f v) := by
  have h : (linearSubstitution f).toLinearMap.comp linearForm = linearForm.comp f := by
    apply Finsupp.lhom_ext'
    intro i
    apply LinearMap.ext_ring
    simp [LinearMap.comp_apply]
  exact LinearMap.congr_fun h v

/-- Linear substitution preserves each homogeneous degree. -/
def linearGradedMap (f : (ι →₀ R) →ₗ[R] (κ →₀ R)) : grading R ι →+*ᵍ grading R κ where
  __ := (linearSubstitution f).toRingHom
  map_mem {n} {p} hp := by
    change (linearSubstitution f p).IsHomogeneous n
    simpa only [linearSubstitution, one_mul] using
      (show p.IsHomogeneous n from hp).aeval
        (fun i ↦ linearForm (f (Finsupp.single i 1)))
        (fun i ↦ linearForm_homogeneous (f (Finsupp.single i 1)))

/-- The identity linear map fixes every polynomial. -/
lemma linearSubstitution_id : linearSubstitution (LinearMap.id : (ι →₀ R) →ₗ[R] _) =
    AlgHom.id R (MvPolynomial ι R) := by
  ext i : 1
  simp

/-- Polynomial substitution composes in the same order as linear maps. -/
lemma linearSubstitution_comp (f : (ι →₀ R) →ₗ[R] (κ →₀ R))
    (g : (κ →₀ R) →ₗ[R] (ν →₀ R)) :
    (linearSubstitution g).comp (linearSubstitution f) = linearSubstitution (g.comp f) := by
  ext i : 1
  change linearSubstitution g (linearSubstitution f (X i)) =
    linearSubstitution (g.comp f) (X i)
  rw [linearSubstitution_X, linearSubstitution_linearForm, linearSubstitution_X]
  rfl

/-- The identity substitution is the graded identity. -/
lemma linearGradedMap_id : linearGradedMap (LinearMap.id : (ι →₀ R) →ₗ[R] _) =
    .id (grading R ι) := by
  ext p : 1
  exact DFunLike.congr_fun linearSubstitution_id p

/-- Successive changes of linear coordinates compose as graded polynomial maps. -/
lemma linearGradedMap_comp (f : (ι →₀ R) →ₗ[R] (κ →₀ R))
    (g : (κ →₀ R) →ₗ[R] (ν →₀ R)) :
    (linearGradedMap g).comp (linearGradedMap f) = linearGradedMap (g.comp f) := by
  ext p : 1
  exact DFunLike.congr_fun (linearSubstitution_comp f g) p

end FLT.Mazur.ProjectiveSpace

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLinearIsomorphism
public import FLT.Mazur.ProjectiveSpaceCoefficientMap

/-!
# Linear projective transitions under coefficient change

A commuting square of linear coordinate maps induces the corresponding
commuting square of graded rings and actual projective schemes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.ProjectiveSpace
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) {ι κ : Type u}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Apply the coefficient homomorphism to each coordinate of a finite-support vector. -/
def changeCoefficients : (ι →₀ R) →+ (ι →₀ S) :=
  Finsupp.mapRange.addMonoidHom φ.toAddMonoidHom

@[simp]
lemma changeCoefficients_single (i : ι) (r : R) :
    changeCoefficients φ (Finsupp.single i r) = Finsupp.single i (φ r) :=
  Finsupp.mapRange_single (hf := φ.map_zero)

/-- Linear forms commute with the coefficient ring homomorphism. -/
lemma map_linearForm (v : ι →₀ R) :
    MvPolynomial.map φ (linearForm v) = linearForm (changeCoefficients φ v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [hv, hw]
  | single i r => simp [smul_eq_C_mul]

/-- A commuting linear square induces a commuting square of graded polynomial rings. -/
lemma linearGradedMap_coefficient (f : (ι →₀ R) →ₗ[R] (κ →₀ R))
    (g : (ι →₀ S) →ₗ[S] (κ →₀ S))
    (h : ∀ v, changeCoefficients φ (f v) = g (changeCoefficients φ v)) :
    (coefficientGradedMap φ κ).comp (linearGradedMap f) =
      (linearGradedMap g).comp (coefficientGradedMap φ ι) := by
  have he : (MvPolynomial.map φ).comp (linearSubstitution f).toRingHom =
      (linearSubstitution g).toRingHom.comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [linearSubstitution]
    · intro i
      change MvPolynomial.map φ (linearSubstitution f (X i)) =
        linearSubstitution g (MvPolynomial.map φ (X i))
      rw [linearSubstitution_X, map_linearForm, h, changeCoefficients_single,
        map_one, map_X, linearSubstitution_X]
  ext p : 1
  exact DFunLike.congr_fun he p

/-- Inverse coordinate changes also commute with coefficient extension. -/
lemma changeCoefficients_inverse (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R))
    (d : (ι →₀ S) ≃ₗ[S] (κ →₀ S))
    (h : ∀ v, changeCoefficients φ (e v) = d (changeCoefficients φ v)) (w : κ →₀ R) :
    changeCoefficients φ (e.symm w) = d.symm (changeCoefficients φ w) := by
  apply d.injective
  rw [d.apply_symm_apply, ← h, e.apply_symm_apply]

/-- Projective coordinate changes commute with the actual change-of-coefficients morphism. -/
lemma linearIso_coefficientMap (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R))
    (d : (ι →₀ S) ≃ₗ[S] (κ →₀ S))
    (h : ∀ v, changeCoefficients φ (e v) = d (changeCoefficients φ v)) :
    coefficientMap φ ι ≫ (linearIso e).hom =
      (linearIso d).hom ≫ coefficientMap φ κ := by
  change Proj.map _ _ ≫ Proj.map _ _ = Proj.map _ _ ≫ Proj.map _ _
  rw [← Proj.map_comp, ← Proj.map_comp]
  congr 1
  exact linearGradedMap_coefficient φ e.symm.toLinearMap d.symm.toLinearMap
    (changeCoefficients_inverse φ e d h)

end FLT.Mazur.ProjectiveSpace

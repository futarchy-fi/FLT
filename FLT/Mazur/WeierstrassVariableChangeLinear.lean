/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeHomogeneous
public import FLT.Mazur.ProjectiveLinearOver

/-!
# The invertible linear substitution of an admissible change

The three homogeneous linear forms extend to an actual free-module
equivalence and hence to a projective-space isomorphism over the base.
-/

@[expose] public noncomputable section

open WeierstrassCurve MvPolynomial CategoryTheory

namespace FLT.Mazur.WeierstrassVariableChangeLinear

variable {R : Type} [CommRing R] (C D : VariableChange R)

/-- The columns of the homogeneous substitution on linear polynomials. -/
def columns : Fin 3 → (Fin 3 →₀ R) :=
  ![(C.u : R) ^ 2 • Finsupp.single 0 1 + C.r • Finsupp.single 2 1,
    (C.u : R) ^ 3 • Finsupp.single 1 1 +
      ((C.u : R) ^ 2 * C.s) • Finsupp.single 0 1 + C.t • Finsupp.single 2 1,
    Finsupp.single 2 1]

/-- Linear extension of the three specified coordinate forms. -/
def linearMap : (Fin 3 →₀ R) →ₗ[R] (Fin 3 →₀ R) :=
  Finsupp.linearCombination R (columns C)

/-- The linear map has exactly the prescribed columns. -/
@[simp] theorem linearMap_single (i : Fin 3) (r : R) :
    linearMap C (Finsupp.single i r) = r • columns C i :=
  Finsupp.linearCombination_single _ _ _

/-- Identity coordinates induce the identity linear map. -/
@[simp] theorem linearMap_one : linearMap (1 : VariableChange R) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro i r
  fin_cases i <;> simp [columns, VariableChange.one_def]

/-- Successive substitutions agree on the entire free module. -/
theorem linearMap_mul : linearMap (C * D) = (linearMap C).comp (linearMap D) := by
  apply Finsupp.lhom_ext
  intro i r
  simp only [LinearMap.comp_apply, linearMap_single, map_smul]
  congr 1
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [columns, VariableChange.mul_def, map_add] <;> ring

/-- The inverse variable change is a genuine inverse linear map. -/
def linearEquiv : (Fin 3 →₀ R) ≃ₗ[R] (Fin 3 →₀ R) :=
  LinearEquiv.ofLinearMap (linearMap C) (linearMap C⁻¹)
    (by rw [← linearMap_mul, mul_inv_cancel, linearMap_one])
    (by rw [← linearMap_mul, inv_mul_cancel, linearMap_one])

/-- Polynomial substitution sends each variable to its homogeneous coordinate form. -/
theorem substitution_X (i : Fin 3) :
    ProjectiveSpace.linearSubstitution (linearMap C) (X i) =
      WeierstrassVariableChangeHomogeneous.coordinates
        (C.map (algebraMap R (MvPolynomial (Fin 3) R))) X i := by
  fin_cases i <;>
    simp [ProjectiveSpace.linearSubstitution_X, columns,
      WeierstrassVariableChangeHomogeneous.coordinates, VariableChange.map,
      ProjectiveSpace.linearForm_single, Algebra.smul_def]

/-- The associated projective-space isomorphism takes new coordinates to old ones. -/
def projectiveIso : ProjectiveSpace.space R (Fin 3) ≅ ProjectiveSpace.space R (Fin 3) :=
  ProjectiveSpace.linearIso (linearEquiv C).symm

/-- The projective coordinate change preserves the coefficient projection. -/
@[reassoc] theorem projectiveIso_baseProjection :
    (projectiveIso C).hom ≫ ProjectiveSpace.baseProjection R (Fin 3) =
      ProjectiveSpace.baseProjection R (Fin 3) :=
  ProjectiveSpace.linearIso_baseProjection (linearEquiv C).symm

end FLT.Mazur.WeierstrassVariableChangeLinear

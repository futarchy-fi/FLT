/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassAffineEquationEvaluation
public import Mathlib.Algebra.Polynomial.Basis

/-!
# Injective affine evaluation from independent normal monomials

The coordinate ring has its actual coefficient-field basis x^a y^b,
with b at most one. Evaluation is injective whenever these images are
independent for the specified scalar map into the target ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassAffineEquationEvaluation
open Polynomial WeierstrassCurve Module
variable {R S : Type*} [CommRing R] [CommRing S]
  (W : WeierstrassCurve R)

/-- The actual quadratic coordinate ring basis over the original coefficient ring. -/
def normalBasis : Basis (ℕ × Fin 2) R W.toAffine.CoordinateRing :=
  (basisMonomials R).smulTower (Affine.CoordinateRing.basis W.toAffine)

/-- This basis consists of the original x and y coordinate monomials. -/
theorem normalBasis_apply (ab : ℕ × Fin 2) :
    normalBasis W ab =
      algebraMap R[X] W.toAffine.CoordinateRing (X ^ ab.1) *
        AdjoinRoot.root W.toAffine.polynomial ^ ab.2.val := by
  simp only [normalBasis, Basis.smulTower_apply, coe_basisMonomials, monomial_one_right_eq_X_pow,
    Affine.CoordinateRing.basis_apply, Algebra.smul_def]
  rfl

variable (φ : R →+* S) (x y : S) (he : (W.map φ).toAffine.Equation x y)

/-- Coordinate evaluation as a linear map for its specified target scalar action. -/
def evaluationLinear : let _ := Module.compHom S φ; W.toAffine.CoordinateRing →ₗ[R] S := by
  let _ := Module.compHom S φ
  exact
    { toFun := evaluation W φ x y he
      map_add' := map_add _
      map_smul' := fun a z ↦ by
        change evaluation W φ x y he (a • z) = φ a * evaluation W φ x y he z
        rw [Algebra.smul_def, map_mul, evaluation_scalar] }

/-- Each basis vector evaluates to the indicated pair of coordinate powers. -/
theorem evaluation_normalBasis (ab : ℕ × Fin 2) :
    evaluation W φ x y he (normalBasis W ab) = x ^ ab.1 * y ^ ab.2.val := by
  simp only [normalBasis_apply, map_mul, map_pow, evaluation_x, evaluation_y]

/-- Independent images of the normal monomials make coordinate evaluation injective. -/
theorem evaluation_injective
    (hv : let _ := Module.compHom S φ
      LinearIndependent R (fun ab : ℕ × Fin 2 ↦ x ^ ab.1 * y ^ ab.2.val)) :
    Function.Injective (evaluation W φ x y he) := by
  let _ := Module.compHom S φ
  have hb : LinearIndependent R (fun ab ↦ evaluationLinear W φ x y he (normalBasis W ab)) := by
    simpa only [evaluationLinear, LinearMap.coe_mk, AddHom.coe_mk,
      evaluation_normalBasis] using hv
  have hi := (normalBasis W).injective_constr_of_linearIndependent (R₂ := R) hb
  rw [Basis.constr_self] at hi
  exact hi

end FLT.Mazur.WeierstrassAffineEquationEvaluation

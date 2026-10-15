/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.QuadraticIncidenceTranslation

/-!
# The full quadratic incidence involution

Reflection of the slope exchanges the two tangent directions, preserving
both the incidence coefficient and the horizontal quadratic at every scale.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.QuadraticIncidenceTranslation
variable {R : Type*} [CommRing R] (t s a b : R)
local notation "A" => AdjoinRoot (polynomial t s a b)
local notation "v" => AdjoinRoot.root (polynomial t s a b)

/-- Reflection evaluates the entire original incidence equation. -/
def reflection : A →ₐ[R] A :=
  AdjoinRoot.liftAlgHom (polynomial t s a b) (Algebra.ofId R A)
    (-v - algebraMap R A a) (by
      change (C t * (X ^ 2 + C a * X - C b) - C s).eval₂
        (algebraMap R A) (-v - algebraMap R A a) = 0
      simp only [eval₂_sub, eval₂_mul, eval₂_add, eval₂_pow, eval₂_X,
        eval₂_C, sub_eq_zero]
      linear_combination relation t s a b)

/-- The actual reflected slope. -/
@[simp] theorem reflection_root : reflection t s a b v = -v - algebraMap R A a :=
  AdjoinRoot.liftAlgHom_root ..

/-- Reflecting twice is the identity on every original function. -/
theorem reflection_comp :
    (reflection t s a b).comp (reflection t s a b) = AlgHom.id R A := by
  apply AdjoinRoot.algHom_ext
  simp only [AlgHom.comp_apply, reflection_root, map_sub, map_neg, AlgHom.commutes,
    AlgHom.id_apply]
  ring

/-- The involution of the complete incidence algebra, with its explicit inverse. -/
def reflectionEquiv : A ≃ₐ[R] A :=
  AlgEquiv.ofAlgHom (reflection t s a b) (reflection t s a b)
    (reflection_comp t s a b) (reflection_comp t s a b)

/-- The inverse involution is the same substitution. -/
theorem reflectionEquiv_symm : (reflectionEquiv t s a b).symm = reflectionEquiv t s a b :=
  rfl

/-- The horizontal quadratic is invariant under reflection. -/
theorem reflection_horizontal :
    reflection t s a b (v ^ 2 + algebraMap R A a * v - algebraMap R A b) =
      v ^ 2 + algebraMap R A a * v - algebraMap R A b := by
  simp only [map_sub, map_add, map_mul, map_pow, AlgHom.commutes, reflection_root]
  ring

end FLT.Mazur.QuadraticIncidenceTranslation

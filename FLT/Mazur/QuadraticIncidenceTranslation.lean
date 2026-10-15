/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Tactic.LinearCombination

/-!
# Translation of a quadratic incidence equation across its full chart

A root of the conic quadratic gives inverse translations of the entire
equation t(v²+av-b)=s. Neither t nor the smoothing parameter is inverted.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.QuadraticIncidenceTranslation
variable {R : Type*} [CommRing R] (t s a b r : R)

/-- The unsplit incidence equation over an arbitrary coefficient algebra. -/
def polynomial : R[X] := C t * (X ^ 2 + C a * X - C b) - C s

/-- The translated equation with its two explicit tangent factors. -/
def splitPolynomial : R[X] := C t * (X * (X + C (r + r + a))) - C s

local notation "A" => AdjoinRoot (polynomial t s a b)
local notation "B" => AdjoinRoot (splitPolynomial t s a r)

/-- The original universal root satisfies the entire incidence equation. -/
theorem relation :
    algebraMap R A t * (AdjoinRoot.root (polynomial t s a b) ^ 2 +
      algebraMap R A a * AdjoinRoot.root (polynomial t s a b) - algebraMap R A b) =
        algebraMap R A s := by
  have h := AdjoinRoot.eval₂_root (polynomial t s a b)
  change (C t * (X ^ 2 + C a * X - C b) - C s).eval₂ (algebraMap R A) _ = 0 at h
  simpa only [eval₂_sub, eval₂_mul, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_C, sub_eq_zero] using h

/-- The translated universal root satisfies the two-factor incidence equation. -/
theorem split_relation :
    algebraMap R B t * (AdjoinRoot.root (splitPolynomial t s a r) *
      (AdjoinRoot.root (splitPolynomial t s a r) + algebraMap R B (r + r + a))) =
        algebraMap R B s := by
  have h := AdjoinRoot.eval₂_root (splitPolynomial t s a r)
  change (C t * (X * (X + C (r + r + a))) - C s).eval₂ (algebraMap R B) _ = 0 at h
  simpa only [eval₂_sub, eval₂_mul, eval₂_add, eval₂_X,
    eval₂_C, sub_eq_zero] using h

variable (hr : r ^ 2 + a * r = b)

/-- Adding the selected conic root evaluates every original incidence function. -/
def forward : A →ₐ[R] B :=
  AdjoinRoot.liftAlgHom (polynomial t s a b) (Algebra.ofId R B)
    (AdjoinRoot.root (splitPolynomial t s a r) + algebraMap R B r) (by
      simp only [polynomial, eval₂_sub, eval₂_mul, eval₂_add, eval₂_pow, eval₂_X,
        eval₂_C, AlgHom.coe_toRingHom, Algebra.ofId_apply, sub_eq_zero]
      have he := split_relation t s a r
      have hh := congrArg (algebraMap R B) hr
      simp only [map_add, map_mul, map_pow] at he hh
      linear_combination he + algebraMap R B t * hh)

/-- Subtracting the selected conic root evaluates every split incidence function. -/
def backward : B →ₐ[R] A :=
  AdjoinRoot.liftAlgHom (splitPolynomial t s a r) (Algebra.ofId R A)
    (AdjoinRoot.root (polynomial t s a b) - algebraMap R A r) (by
      simp only [splitPolynomial, eval₂_sub, eval₂_mul, eval₂_add, eval₂_X,
        eval₂_C, AlgHom.coe_toRingHom, Algebra.ofId_apply, map_add, sub_eq_zero]
      have he := relation t s a b
      have hh := congrArg (algebraMap R A) hr
      simp only [map_add, map_mul, map_pow] at hh
      linear_combination he - algebraMap R A t * hh)

/-- The forward substitution is the displayed translation on the universal slope. -/
@[simp] theorem forward_root :
    forward t s a b r hr (AdjoinRoot.root (polynomial t s a b)) =
      AdjoinRoot.root (splitPolynomial t s a r) + algebraMap R B r :=
  AdjoinRoot.liftAlgHom_root ..

/-- The inverse substitution subtracts the same polynomial root. -/
@[simp] theorem backward_root :
    backward t s a b r hr (AdjoinRoot.root (splitPolynomial t s a r)) =
      AdjoinRoot.root (polynomial t s a b) - algebraMap R A r :=
  AdjoinRoot.liftAlgHom_root ..

/-- The full original incidence algebra is the explicit two-factor algebra. -/
def equiv : A ≃ₐ[R] B :=
  AlgEquiv.ofAlgHom (forward t s a b r hr) (backward t s a b r hr)
    (by
      apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply, backward_root, map_sub, forward_root,
        AlgHom.commutes, AlgHom.id_apply, add_sub_cancel_right])
    (by
      apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply, forward_root, map_add, backward_root,
        AlgHom.commutes, AlgHom.id_apply, sub_add_cancel])

end FLT.Mazur.QuadraticIncidenceTranslation

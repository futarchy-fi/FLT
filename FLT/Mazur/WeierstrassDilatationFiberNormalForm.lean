/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberAlgebra

/-!
# The actual split residue chart in tangent coordinates

When the scale and the three indicated coefficients vanish, the invertible
linear substitution p = v, q = v + a₁u identifies the divided chart with pq = c.
The inverse is u = a₁⁻¹(q-p), v = p. This is an algebra equivalence, so it
identifies the entire fiber scheme, including its nonreduced test points.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassDilatation

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (a : Rˣ) (c : R)
  (h1 : W.a₁ = a) (h2 : W.a₂ = 0)

include h1 h2 in
/-- In the split special fiber the tangent coordinates have product c. -/
theorem fiber_tangent_relation :
    y W 0 0 0 c * (y W 0 0 0 c + algebraMap R _ a * x W 0 0 0 c) =
      algebraMap R _ c := by
  have h := equation W 0 0 0 c
  simp only [h1, h2, map_zero, zero_mul, add_zero, zero_add] at h
  linear_combination h

include h1 h2 in
/-- The inverse linear substitution satisfies the actual divided equation. -/
theorem fiber_inverse_equation :
    let u := algebraMap R (NodalFiber.Coordinate c) (↑a⁻¹ : R) *
      (NodalFiber.q c - NodalFiber.p c)
    let v := NodalFiber.p c
    v ^ 2 + (algebraMap R _ W.a₁ * u + algebraMap R _ 0) * v =
      algebraMap R _ 0 * u ^ 3 + algebraMap R _ W.a₂ * u ^ 2 +
        algebraMap R _ 0 * u + algebraMap R _ c := by
  dsimp only
  simp only [h1, h2, map_zero, zero_mul, add_zero, zero_add]
  have hi : algebraMap R (NodalFiber.Coordinate c) (↑a : R) *
      algebraMap R _ (↑a⁻¹ : R) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  rw [← mul_assoc, hi, one_mul]
  linear_combination NodalFiber.relation c

/-- The actual fiber maps into tangent-coordinate functions by the inverse substitution. -/
def fiberToTangent : Coordinate W 0 0 0 c →ₐ[R] NodalFiber.Coordinate c :=
  evaluation W 0 0 0 c
    (algebraMap R _ (↑a⁻¹ : R) * (NodalFiber.q c - NodalFiber.p c)) (NodalFiber.p c)
    (fiber_inverse_equation W a c h1 h2)

/-- The tangent-coordinate algebra maps back using the actual two tangent factors. -/
def tangentToFiber : NodalFiber.Coordinate c →ₐ[R] Coordinate W 0 0 0 c :=
  NodalFiber.evaluation c (y W 0 0 0 c)
    (y W 0 0 0 c + algebraMap R _ a * x W 0 0 0 c)
    (fiber_tangent_relation W a c h1 h2)

/-- The forward map sends u to the difference of tangent factors divided by a₁. -/
@[simp] theorem fiberToTangent_x :
    fiberToTangent W a c h1 h2 (x W 0 0 0 c) =
      algebraMap R _ (↑a⁻¹ : R) * (NodalFiber.q c - NodalFiber.p c) :=
  evaluation_x _ _ _ _ _ _ _ _

/-- The forward map sends v to the first tangent factor. -/
@[simp] theorem fiberToTangent_y :
    fiberToTangent W a c h1 h2 (y W 0 0 0 c) = NodalFiber.p c :=
  evaluation_y _ _ _ _ _ _ _ _

/-- The first tangent factor pulls back to v. -/
@[simp] theorem tangentToFiber_p :
    tangentToFiber W a c h1 h2 (NodalFiber.p c) = y W 0 0 0 c :=
  NodalFiber.evaluation_p _ _ _ _

/-- The second tangent factor pulls back to v + a₁u. -/
@[simp] theorem tangentToFiber_q :
    tangentToFiber W a c h1 h2 (NodalFiber.q c) =
      y W 0 0 0 c + algebraMap R _ a * x W 0 0 0 c :=
  NodalFiber.evaluation_q _ _ _ _

/-- The tangent substitution is invertible on the whole actual fiber algebra. -/
def fiberTangentEquiv : Coordinate W 0 0 0 c ≃ₐ[R] NodalFiber.Coordinate c := by
  apply AlgEquiv.ofAlgHom (fiberToTangent W a c h1 h2) (tangentToFiber W a c h1 h2)
  · apply NodalFiber.hom_ext
    · simp
    · simp only [AlgHom.comp_apply, tangentToFiber_q, map_add, map_mul,
        AlgHom.commutes, fiberToTangent_y, fiberToTangent_x, AlgHom.id_apply]
      rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
      ring
  · apply hom_ext
    · simp only [AlgHom.comp_apply, fiberToTangent_x, map_mul, map_sub,
        AlgHom.commutes, tangentToFiber_q, tangentToFiber_p, AlgHom.id_apply]
      rw [add_sub_cancel_left, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    · simp

end FLT.Mazur.WeierstrassDilatation

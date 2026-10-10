/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineMonicComparison
public import FLT.Mazur.WeierstrassFlatSectionRegular
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# The flat affine algebra for a scaled nodal chart

Substituting x = s u and y = s v and cancelling s² gives a monic quadratic
in v. This defines an actual flat algebra, not just a condition on rational
points. The coefficient hypotheses needed to map it to the original cubic
are kept separate from the algebra construction.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.WeierstrassDilatation

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The equation after dividing the original affine equation by the common factor s². -/
def polynomial : R[X][X] :=
  X ^ 2 + C (C W.a₁ * X + C b3) * X -
    C (C s * X ^ 3 + C W.a₂ * X ^ 2 + C b4 * X + C b6)

/-- Evaluation exposes the actual divided equation. -/
theorem polynomial_eval {S : Type*} [CommRing S] (f : R[X] →+* S) (y : S) :
    (polynomial W s b3 b4 b6).eval₂ f y =
      y ^ 2 + (f (C W.a₁) * f X + f (C b3)) * y -
        (f (C s) * f X ^ 3 + f (C W.a₂) * f X ^ 2 + f (C b4) * f X + f (C b6)) := by
  simp only [polynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
    eval₂_C, map_add, map_mul, map_pow]

/-- The transformed equation remains monic even when the scaling parameter is not a unit. -/
theorem polynomial_monic : (polynomial W s b3 b4 b6).Monic := by
  have he : polynomial W s b3 b4 b6 = Cubic.toPoly
      ⟨0, 1, C W.a₁ * X + C b3,
        -(C s * X ^ 3 + C W.a₂ * X ^ 2 + C b4 * X + C b6)⟩ := by
    simp only [polynomial, Cubic.toPoly, C_0, C_1, C_neg, zero_mul, one_mul, zero_add]
    ring
  rw [he]
  exact Cubic.monic_of_b_eq_one'

/-- The actual affine coordinate algebra of the divided equation. -/
abbrev Coordinate := AdjoinRoot (polynomial W s b3 b4 b6)

/-- The first coordinate of the divided chart. -/
def x : Coordinate W s b3 b4 b6 := algebraMap R[X] _ X

/-- The second coordinate of the divided chart. -/
def y : Coordinate W s b3 b4 b6 := AdjoinRoot.root (polynomial W s b3 b4 b6)

/-- The universal divided coordinates satisfy their defining equation. -/
theorem equation :
    y W s b3 b4 b6 ^ 2 +
        (algebraMap R _ W.a₁ * x W s b3 b4 b6 + algebraMap R _ b3) * y W s b3 b4 b6 =
      algebraMap R _ s * x W s b3 b4 b6 ^ 3 +
        algebraMap R _ W.a₂ * x W s b3 b4 b6 ^ 2 +
        algebraMap R _ b4 * x W s b3 b4 b6 + algebraMap R _ b6 := by
  have h := AdjoinRoot.eval₂_root (polynomial W s b3 b4 b6)
  rw [polynomial_eval] at h
  have hc (a : R) : algebraMap R[X] (Coordinate W s b3 b4 b6) (C a) =
      algebraMap R _ a := (IsScalarTower.algebraMap_apply R R[X] _ a).symm
  simpa only [AdjoinRoot.algebraMap_eq, ← hc, sub_eq_zero, x, y] using h

/-- The chart is free over its affine coordinate line. -/
instance coordinate_free_line : Module.Free R[X] (Coordinate W s b3 b4 b6) :=
  (polynomial_monic W s b3 b4 b6).free_adjoinRoot

/-- The chart is flat over its original coefficient ring. -/
instance coordinate_flat : Module.Flat R (Coordinate W s b3 b4 b6) :=
  Module.Flat.trans R R[X] (Coordinate W s b3 b4 b6)

/-- A regular scaling parameter remains regular in the actual chart algebra. -/
theorem scale_regular (hs : IsRegular s) :
    IsRegular (algebraMap R (Coordinate W s b3 b4 b6) s) :=
  WeierstrassIntegralChart.flatRingHom_isRegular _
    (RingHom.flat_algebraMap_iff.mpr inferInstance) hs

/-- Evaluation on any actual solution of the divided equation. -/
def evaluation {S : Type*} [CommRing S] [Algebra R S] (u v : S)
    (h : v ^ 2 + (algebraMap R S W.a₁ * u + algebraMap R S b3) * v =
      algebraMap R S s * u ^ 3 + algebraMap R S W.a₂ * u ^ 2 +
        algebraMap R S b4 * u + algebraMap R S b6) :
    Coordinate W s b3 b4 b6 →ₐ[R] S :=
  AdjoinRoot.liftAlgHom (polynomial W s b3 b4 b6) (aeval u) v (by
    rw [polynomial_eval]
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C, aeval_X,
      sub_eq_zero] using h)

/-- Evaluation preserves the first coordinate. -/
@[simp] theorem evaluation_x {S : Type*} [CommRing S] [Algebra R S] (u v : S)
    (h : v ^ 2 + (algebraMap R S W.a₁ * u + algebraMap R S b3) * v =
      algebraMap R S s * u ^ 3 + algebraMap R S W.a₂ * u ^ 2 +
        algebraMap R S b4 * u + algebraMap R S b6) :
    evaluation W s b3 b4 b6 u v h (x W s b3 b4 b6) = u := by
  simp [evaluation, x, AdjoinRoot.algebraMap_eq, AdjoinRoot.liftAlgHom_of]

/-- Evaluation preserves the second coordinate. -/
@[simp] theorem evaluation_y {S : Type*} [CommRing S] [Algebra R S] (u v : S)
    (h : v ^ 2 + (algebraMap R S W.a₁ * u + algebraMap R S b3) * v =
      algebraMap R S s * u ^ 3 + algebraMap R S W.a₂ * u ^ 2 +
        algebraMap R S b4 * u + algebraMap R S b6) :
    evaluation W s b3 b4 b6 u v h (y W s b3 b4 b6) = v :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The two actual coordinates determine every algebra map out of the divided chart. -/
@[ext] theorem hom_ext {S : Type*} [CommRing S] [Algebra R S]
    (f g : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (hx : f (x W s b3 b4 b6) = g (x W s b3 b4 b6))
    (hy : f (y W s b3 b4 b6) = g (y W s b3 b4 b6)) : f = g := by
  apply AdjoinRoot.algHom_ext'
  · exact Polynomial.algHom_ext hx
  · exact hy

end FLT.Mazur.WeierstrassDilatation

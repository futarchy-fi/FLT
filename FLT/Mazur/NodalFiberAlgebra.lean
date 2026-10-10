/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationAlgebra

/-!
# The affine equation pq = c

This actual coordinate algebra describes both the two-branch residue node
and the middle-depth hyperbola. Its universal property keeps the two tangent
coordinates explicit.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.NodalFiber

variable {R : Type*} [CommRing R] (c : R)

/-- The relation is linear in the second variable over the first coordinate line. -/
def polynomial : R[X][X] := C X * X - C (C c)

/-- Evaluation exposes the product relation. -/
theorem polynomial_eval {S : Type*} [CommRing S] (f : R[X] →+* S) (v : S) :
    (polynomial c).eval₂ f v = f X * v - f (C c) := by
  simp only [polynomial, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X]

/-- The affine algebra with product of its coordinates equal to c. -/
abbrev Coordinate := AdjoinRoot (polynomial c)

/-- The first tangent coordinate. -/
def p : Coordinate c := algebraMap R[X] _ X

/-- The second tangent coordinate. -/
def q : Coordinate c := AdjoinRoot.root (polynomial c)

/-- The universal tangent coordinates have the prescribed product. -/
theorem relation : p c * q c = algebraMap R _ c := by
  have h := AdjoinRoot.eval₂_root (polynomial c)
  rw [polynomial_eval] at h
  have hc : algebraMap R[X] (Coordinate c) (C c) = algebraMap R _ c :=
    (IsScalarTower.algebraMap_apply R R[X] _ c).symm
  simpa only [AdjoinRoot.algebraMap_eq, ← hc, sub_eq_zero, p, q] using h

/-- Every pair with product c gives an actual algebra map out of the fiber. -/
def evaluation {S : Type*} [CommRing S] [Algebra R S] (u v : S)
    (h : u * v = algebraMap R S c) : Coordinate c →ₐ[R] S :=
  AdjoinRoot.liftAlgHom (polynomial c) (aeval u) v (by
    simpa only [polynomial, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X, aeval_C, sub_eq_zero] using h)

/-- Evaluation sends the first universal coordinate to its supplied value. -/
@[simp] theorem evaluation_p {S : Type*} [CommRing S] [Algebra R S] (u v : S)
    (h : u * v = algebraMap R S c) : evaluation c u v h (p c) = u := by
  simp [evaluation, p, AdjoinRoot.algebraMap_eq, AdjoinRoot.liftAlgHom_of]

/-- Evaluation sends the second universal coordinate to its supplied value. -/
@[simp] theorem evaluation_q {S : Type*} [CommRing S] [Algebra R S] (u v : S)
    (h : u * v = algebraMap R S c) : evaluation c u v h (q c) = v :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Maps out of this affine fiber are determined by their tangent coordinates. -/
@[ext] theorem hom_ext {S : Type*} [CommRing S] [Algebra R S]
    (f g : Coordinate c →ₐ[R] S) (hp : f (p c) = g (p c))
    (hq : f (q c) = g (q c)) : f = g := by
  apply AdjoinRoot.algHom_ext'
  · exact Polynomial.algHom_ext hp
  · exact hq

end FLT.Mazur.NodalFiber

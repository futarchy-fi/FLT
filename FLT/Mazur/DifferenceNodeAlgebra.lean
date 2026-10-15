/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberAlgebra

/-!
# A product equation corrected by the tangent difference

The quotient has the exact relation pq = h(q-p-b). This intermediate algebra
retains every coefficient before the terminal smoothing constant is extracted.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.DifferenceNode
variable {R : Type*} [CommRing R] (h : R[X]) (b : R)

/-- The two-variable equation with its entire difference correction. -/
def polynomial : R[X][X] :=
  C X * X - (h.map C).comp (X - C X - C (C b))

/-- Evaluation keeps the original correction polynomial. -/
theorem polynomial_eval {S : Type*} [CommRing S] (f : R[X] →+* S) (v : S) :
    (polynomial h b).eval₂ f v =
      f X * v - h.eval₂ (f.comp C) (v - f X - f (C b)) := by
  simp only [polynomial, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X, eval₂_comp, eval₂_map]

/-- The actual quotient defined by the corrected product equation. -/
abbrev Coordinate := AdjoinRoot (polynomial h b)

/-- The first tangent coordinate of the corrected quotient. -/
def p : Coordinate h b := algebraMap R[X] _ X

/-- The second tangent coordinate of the corrected quotient. -/
def q : Coordinate h b := AdjoinRoot.root (polynomial h b)

/-- The universal coordinates satisfy the full corrected relation. -/
theorem relation : p h b * q h b =
    h.eval₂ (algebraMap R (Coordinate h b))
      (q h b - p h b - algebraMap R (Coordinate h b) b) := by
  have he := AdjoinRoot.eval₂_root (polynomial h b)
  rw [polynomial_eval] at he
  have hc : (algebraMap R[X] (Coordinate h b)).comp C =
      algebraMap R (Coordinate h b) := (IsScalarTower.algebraMap_eq R R[X] _).symm
  change p h b * q h b - h.eval₂
    ((algebraMap R[X] (Coordinate h b)).comp C)
    (q h b - p h b - algebraMap R[X] (Coordinate h b) (C b)) = 0 at he
  rw [hc] at he
  have hb : algebraMap R (Coordinate h b) b =
      algebraMap R[X] (Coordinate h b) (C b) :=
    IsScalarTower.algebraMap_apply R R[X] (Coordinate h b) b
  rw [← hb, sub_eq_zero] at he
  exact he

/-- Any pair satisfying the full relation defines a map from the quotient. -/
def evaluation {S : Type*} [CommRing S] [Algebra R S] (u v : S)
    (he : u * v = h.eval₂ (algebraMap R S) (v - u - algebraMap R S b)) :
    Coordinate h b →ₐ[R] S :=
  AdjoinRoot.liftAlgHom (polynomial h b) (aeval u) v (by
    rw [polynomial_eval]
    have hc : ((aeval u : R[X] →ₐ[R] S) : R[X] →+* S).comp C =
        algebraMap R S := by
      ext a
      exact aeval_C u a
    rw [hc]
    simpa only [AlgHom.coe_toRingHom, aeval_X, aeval_C, sub_eq_zero] using he)

/-- Evaluation preserves the first coordinate. -/
@[simp] theorem evaluation_p {S : Type*} [CommRing S] [Algebra R S] (u v : S)
    (he : u * v = h.eval₂ (algebraMap R S) (v - u - algebraMap R S b)) :
    evaluation h b u v he (p h b) = u := by
  simp [evaluation, p, AdjoinRoot.algebraMap_eq, AdjoinRoot.liftAlgHom_of]

/-- Evaluation preserves the second coordinate. -/
@[simp] theorem evaluation_q {S : Type*} [CommRing S] [Algebra R S] (u v : S)
    (he : u * v = h.eval₂ (algebraMap R S) (v - u - algebraMap R S b)) :
    evaluation h b u v he (q h b) = v := AdjoinRoot.liftAlgHom_root ..

/-- The two tangent coordinates determine a map on every quotient function. -/
@[ext] theorem hom_ext {S : Type*} [CommRing S] [Algebra R S]
    (f g : Coordinate h b →ₐ[R] S) (hp : f (p h b) = g (p h b))
    (hq : f (q h b) = g (q h b)) : f = g := by
  apply AdjoinRoot.algHom_ext'
  · exact Polynomial.algHom_ext hp
  · exact hq

end FLT.Mazur.DifferenceNode

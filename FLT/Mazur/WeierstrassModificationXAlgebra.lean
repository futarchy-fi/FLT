/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationAlgebra

/-!
# The x-direction equation chart for the nodal modification

Put t = s/x and v = y/x. After dividing the original equation by x²,
x = v² + (a₁+b₃t)v - (a₂+b₄t+b₆t²). Eliminating x gives the actual
algebra t*x(t,v) = s. Its contraction and overlap maps are separate proofs;
no global blowup, flatness or properness property is asserted here.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.WeierstrassModificationX

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The x-direction relation, with the incidence coordinate as coefficient variable. -/
def polynomial : R[X][X] :=
  C X * (X ^ 2 + C (C W.a₁ + C b3 * X) * X -
    C (C W.a₂ + C b4 * X + C b6 * X ^ 2)) - C (C s)

/-- Evaluation displays the actual incidence equation. -/
theorem polynomial_eval {S : Type*} [CommRing S] (f : R[X] →+* S) (v : S) :
    (polynomial W s b3 b4 b6).eval₂ f v =
      f X * (v ^ 2 + (f (C W.a₁) + f (C b3) * f X) * v -
        (f (C W.a₂) + f (C b4) * f X + f (C b6) * f X ^ 2)) - f (C s) := by
  simp only [polynomial, eval₂_sub, eval₂_mul, eval₂_add, eval₂_pow, eval₂_C,
    eval₂_X, map_add, map_mul, map_pow]

/-- The actual two-variable equation algebra. -/
abbrev Coordinate := AdjoinRoot (polynomial W s b3 b4 b6)

/-- The coordinate representing s/x. -/
def t : Coordinate W s b3 b4 b6 := algebraMap R[X] _ X

/-- The coordinate representing y/x. -/
def v : Coordinate W s b3 b4 b6 := AdjoinRoot.root (polynomial W s b3 b4 b6)

/-- The original horizontal coordinate recovered from the divided cubic equation. -/
def x : Coordinate W s b3 b4 b6 :=
  v W s b3 b4 b6 ^ 2 +
    (algebraMap R _ W.a₁ + algebraMap R _ b3 * t W s b3 b4 b6) * v W s b3 b4 b6 -
      (algebraMap R _ W.a₂ + algebraMap R _ b4 * t W s b3 b4 b6 +
        algebraMap R _ b6 * t W s b3 b4 b6 ^ 2)

/-- The original vertical coordinate. -/
def y : Coordinate W s b3 b4 b6 := x W s b3 b4 b6 * v W s b3 b4 b6

/-- The universal incidence relation retains the original scale. -/
theorem incidence : t W s b3 b4 b6 * x W s b3 b4 b6 = algebraMap R _ s := by
  have h := AdjoinRoot.eval₂_root (polynomial W s b3 b4 b6)
  rw [polynomial_eval] at h
  have hc (a : R) : algebraMap R[X] (Coordinate W s b3 b4 b6) (C a) =
      algebraMap R _ a := (IsScalarTower.algebraMap_apply R R[X] _ a).symm
  simpa only [AdjoinRoot.algebraMap_eq, ← hc, sub_eq_zero, t, v, x] using h

/-- Every solution of the incidence equation gives an actual chart map. -/
def evaluation {S : Type*} [CommRing S] [Algebra R S] (a b : S)
    (h : a * (b ^ 2 + (algebraMap R S W.a₁ + algebraMap R S b3 * a) * b -
      (algebraMap R S W.a₂ + algebraMap R S b4 * a + algebraMap R S b6 * a ^ 2)) =
        algebraMap R S s) : Coordinate W s b3 b4 b6 →ₐ[R] S :=
  AdjoinRoot.liftAlgHom (polynomial W s b3 b4 b6) (aeval a) b (by
    rw [polynomial_eval]
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C, aeval_X,
      sub_eq_zero] using h)

/-- Evaluation preserves the incidence coordinate. -/
@[simp] theorem evaluation_t {S : Type*} [CommRing S] [Algebra R S] (a b : S)
    (h : a * (b ^ 2 + (algebraMap R S W.a₁ + algebraMap R S b3 * a) * b -
      (algebraMap R S W.a₂ + algebraMap R S b4 * a + algebraMap R S b6 * a ^ 2)) =
        algebraMap R S s) : evaluation W s b3 b4 b6 a b h (t W s b3 b4 b6) = a := by
  simp [evaluation, t, AdjoinRoot.algebraMap_eq, AdjoinRoot.liftAlgHom_of]

/-- Evaluation preserves the slope coordinate. -/
@[simp] theorem evaluation_v {S : Type*} [CommRing S] [Algebra R S] (a b : S)
    (h : a * (b ^ 2 + (algebraMap R S W.a₁ + algebraMap R S b3 * a) * b -
      (algebraMap R S W.a₂ + algebraMap R S b4 * a + algebraMap R S b6 * a ^ 2)) =
        algebraMap R S s) : evaluation W s b3 b4 b6 a b h (v W s b3 b4 b6) = b :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The two incidence coordinates determine a chart map. -/
@[ext] theorem hom_ext {S : Type*} [CommRing S] [Algebra R S]
    (f g : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (ht : f (t W s b3 b4 b6) = g (t W s b3 b4 b6))
    (hv : f (v W s b3 b4 b6) = g (v W s b3 b4 b6)) : f = g := by
  apply AdjoinRoot.algHom_ext'
  · exact Polynomial.algHom_ext ht
  · exact hv

end FLT.Mazur.WeierstrassModificationX

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXAlgebra

/-!
# The actual horizontal residue equation

The normal form is t*(v*(v+a)-c*t²)=0. Before the middle depth c vanishes,
giving the three lines t=0, v=0, v=-a; the middle-depth equation keeps c.
The algebra comparison preserves the actual incidence and slope coordinates.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.WeierstrassModificationX

variable {R : Type*} [CommRing R] (a c : R)

/-- The two-variable horizontal fiber polynomial, retaining its constant-depth coefficient. -/
def fiberPolynomial : R[X][X] := C X * (X * (X + C (C a)) - C (C c * X ^ 2))

/-- Evaluation retains the three factors and the middle-depth coefficient. -/
theorem fiberPolynomial_eval {S : Type*} [CommRing S] (f : R[X] →+* S) (w : S) :
    (fiberPolynomial a c).eval₂ f w =
      f X * (w * (w + f (C a)) - f (C c) * f X ^ 2) := by
  simp only [fiberPolynomial, eval₂_mul, eval₂_sub, eval₂_add, eval₂_C, eval₂_X,
    eval₂_pow, map_mul, map_pow]

/-- The full horizontal fiber algebra, with no discarded components or reducedness assumption. -/
abbrev FiberCoordinate := AdjoinRoot (fiberPolynomial a c)

/-- The original incidence ratio in the fiber normal form. -/
def fiberT : FiberCoordinate a c := algebraMap R[X] _ X

/-- The original tangent slope in the fiber normal form. -/
def fiberV : FiberCoordinate a c := AdjoinRoot.root (fiberPolynomial a c)

/-- The full normal-form equation holds in its coordinate algebra. -/
theorem fiber_relation :
    fiberT a c * (fiberV a c * (fiberV a c + algebraMap R _ a) -
      algebraMap R _ c * fiberT a c ^ 2) = 0 := by
  have h := AdjoinRoot.eval₂_root (fiberPolynomial a c)
  rw [fiberPolynomial_eval] at h
  have hc (r : R) : algebraMap R[X] (FiberCoordinate a c) (C r) =
      algebraMap R _ r := (IsScalarTower.algebraMap_apply R R[X] _ r).symm
  simpa only [AdjoinRoot.algebraMap_eq, ← hc, fiberT, fiberV] using h

/-- The full horizontal fiber has the expected universal property. -/
def fiberEvaluation {S : Type*} [CommRing S] [Algebra R S] (u w : S)
    (h : u * (w * (w + algebraMap R S a) - algebraMap R S c * u ^ 2) = 0) :
    FiberCoordinate a c →ₐ[R] S :=
  AdjoinRoot.liftAlgHom (fiberPolynomial a c) (aeval u) w (by
    rw [fiberPolynomial_eval]
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C, aeval_X] using h)

/-- Evaluation retains the incidence ratio. -/
@[simp] theorem fiberEvaluation_t {S : Type*} [CommRing S] [Algebra R S] (u w : S)
    (h : u * (w * (w + algebraMap R S a) - algebraMap R S c * u ^ 2) = 0) :
    fiberEvaluation a c u w h (fiberT a c) = u := by
  simp [fiberEvaluation, fiberT, AdjoinRoot.algebraMap_eq, AdjoinRoot.liftAlgHom_of]

/-- Evaluation retains the tangent slope. -/
@[simp] theorem fiberEvaluation_v {S : Type*} [CommRing S] [Algebra R S] (u w : S)
    (h : u * (w * (w + algebraMap R S a) - algebraMap R S c * u ^ 2) = 0) :
    fiberEvaluation a c u w h (fiberV a c) = w := AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Incidence and slope determine every map out of the fiber normal form. -/
theorem fiber_hom_ext {S : Type*} [CommRing S] [Algebra R S]
    (f g : FiberCoordinate a c →ₐ[R] S)
    (ht : f (fiberT a c) = g (fiberT a c))
    (hv : f (fiberV a c) = g (fiberV a c)) : f = g := by
  apply AdjoinRoot.algHom_ext'
  · exact Polynomial.algHom_ext ht
  · exact hv

variable (W : WeierstrassCurve R) (h1 : W.a₁ = a) (h2 : W.a₂ = 0)

include h1 h2 in
/-- The specialized horizontal polynomial is exactly the full fiber normal form. -/
theorem polynomial_eq_fiber : polynomial W 0 0 0 c = fiberPolynomial a c := by
  simp only [polynomial, fiberPolynomial, h1, h2, map_zero, zero_mul, add_zero,
    zero_add, sub_zero]
  ring

/-- Specializing the actual equation gives the full horizontal fiber algebra. -/
def fiberNormalEquiv : Coordinate W 0 0 0 c ≃ₐ[R] FiberCoordinate a c :=
  (AdjoinRoot.algEquivOfEq R[X] _ _ (polynomial_eq_fiber a c W h1 h2)).restrictScalars R

/-- The normal-form comparison retains the original incidence ratio. -/
@[simp] theorem fiberNormalEquiv_t :
    fiberNormalEquiv a c W h1 h2 (t W 0 0 0 c) = fiberT a c :=
  (AdjoinRoot.algEquivOfEq R[X] _ _ (polynomial_eq_fiber a c W h1 h2)).commutes X

/-- The normal-form comparison retains the original tangent slope. -/
@[simp] theorem fiberNormalEquiv_v :
    fiberNormalEquiv a c W h1 h2 (v W 0 0 0 c) = fiberV a c :=
  AdjoinRoot.algEquivOfEq_root _ _ (polynomial_eq_fiber a c W h1 h2)

end FLT.Mazur.WeierstrassModificationX

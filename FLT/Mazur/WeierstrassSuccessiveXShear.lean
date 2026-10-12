/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearData
public import FLT.Mazur.WeierstrassSuccessiveXAlgebra

/-!
# Shearing every original successive incidence chart

The original retained coordinates t and u are fixed, while the slope v
changes by r. Both defining relations are preserved without canceling u.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 r : R)
local notation "U" => rootShearCurve W r
local notation "A" => Coordinate W s π b3 b4 b6
local notation "B" => Coordinate U s π b3 (b4 - r * b3) b6
local notation "a" => coord W s π b3 b4 b6
local notation "b" => coord U s π b3 (b4 - r * b3) b6

/-- The translated slope solves the original successive equation. -/
theorem shearForward_equation :
    (b 1 + algebraMap R B r) ^ 2 +
        (algebraMap R B W.a₁ + algebraMap R B b3 * b 0) * (b 1 + algebraMap R B r) =
      algebraMap R B s * b 2 + algebraMap R B W.a₂ +
        algebraMap R B b4 * b 0 + algebraMap R B b6 * b 0 ^ 2 := by
  have h := equation U s π b3 (b4 - r * b3) b6
  rw [(rootShearCurve_coefficients r).1, (rootShearCurve_coefficients r).2.1] at h
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat] at h
  linear_combination h

/-- The original successive incidence algebra maps to its actual shear. -/
def shearForward : A →ₐ[R] B :=
  evaluation W s π b3 b4 b6 ![b 0, b 1 + algebraMap R B r, b 2]
    (shearForward_equation W s π b3 b4 b6 r) (incidence U s π b3 (b4 - r * b3) b6)

/-- The inverse slope translation solves the actual sheared equation. -/
theorem shearBackward_equation :
    (a 1 - algebraMap R A r) ^ 2 +
        (algebraMap R A (U).a₁ + algebraMap R A b3 * a 0) * (a 1 - algebraMap R A r) =
      algebraMap R A s * a 2 + algebraMap R A (U).a₂ +
        algebraMap R A (b4 - r * b3) * a 0 + algebraMap R A b6 * a 0 ^ 2 := by
  rw [(rootShearCurve_coefficients r).1, (rootShearCurve_coefficients r).2.1]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  linear_combination equation W s π b3 b4 b6

/-- The inverse fixes both incidence coordinates and subtracts r from the slope. -/
def shearBackward : B →ₐ[R] A :=
  evaluation U s π b3 (b4 - r * b3) b6 ![a 0, a 1 - algebraMap R A r, a 2]
    (shearBackward_equation W s π b3 b4 b6 r) (incidence W s π b3 b4 b6)

/-- All original successive coordinates have the prescribed shear formulas. -/
@[simp] theorem shearForward_coord (i : Fin 3) :
    shearForward W s π b3 b4 b6 r (a i) = ![b 0, b 1 + algebraMap R B r, b 2] i :=
  evaluation_coord _ _ _ _ _ _ _ _ _ _

/-- The inverse formulas retain both sides of the original incidence relation. -/
@[simp] theorem shearBackward_coord (i : Fin 3) :
    shearBackward W s π b3 b4 b6 r (b i) = ![a 0, a 1 - algebraMap R A r, a 2] i :=
  evaluation_coord _ _ _ _ _ _ _ _ _ _

/-- Every successive incidence chart is isomorphic to its shear, including u = 0. -/
def shearEquiv : A ≃ₐ[R] B :=
  AlgEquiv.ofAlgHom (shearForward W s π b3 b4 b6 r) (shearBackward W s π b3 b4 b6 r)
    (by
      apply hom_ext
      intro i
      fin_cases i <;> simp [shearForward_coord, shearBackward_coord])
    (by
      apply hom_ext
      intro i
      fin_cases i <;> simp [shearForward_coord, shearBackward_coord])

end FLT.Mazur.WeierstrassSuccessiveX

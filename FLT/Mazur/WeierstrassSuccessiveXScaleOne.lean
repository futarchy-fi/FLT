/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXAlgebra
public import FLT.Mazur.WeierstrassModificationXAlgebra

/-!
# Eliminating the horizontal coordinate at successive scale one

At scale one, the successive equation recovers u as its quadratic expression
in t and v. Eliminating u gives the full original two-variable modification
algebra, with all coefficients retained and no localization or component loss.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (π b3 b4 b6 : R)
local notation "A" => Coordinate W 1 π b3 b4 b6
local notation "B" => WeierstrassModificationX.Coordinate W π b3 b4 b6
local notation "t" => coord W 1 π b3 b4 b6 0
local notation "v" => coord W 1 π b3 b4 b6 1
local notation "u" => coord W 1 π b3 b4 b6 2
local notation "t'" => WeierstrassModificationX.t W π b3 b4 b6
local notation "v'" => WeierstrassModificationX.v W π b3 b4 b6
local notation "x'" => WeierstrassModificationX.x W π b3 b4 b6

/-- The third coordinate at scale one is the full original quadratic expression. -/
theorem scaleOne_horizontal :
    v ^ 2 + (algebraMap R A W.a₁ + algebraMap R A b3 * t) * v -
      (algebraMap R A W.a₂ + algebraMap R A b4 * t + algebraMap R A b6 * t ^ 2) = u := by
  have h := equation W 1 π b3 b4 b6
  rw [map_one, one_mul] at h
  linear_combination h

/-- The full successive algebra evaluates in the original two-coordinate modification algebra. -/
def scaleOneToModification : A →ₐ[R] B :=
  evaluation W 1 π b3 b4 b6 ![t', v', x'] (by
    change v' ^ 2 + (algebraMap R B W.a₁ + algebraMap R B b3 * t') * v' =
      algebraMap R B 1 * x' + algebraMap R B W.a₂ + algebraMap R B b4 * t' +
        algebraMap R B b6 * t' ^ 2
    rw [map_one, one_mul, WeierstrassModificationX.x]
    ring) (WeierstrassModificationX.incidence W π b3 b4 b6)

/-- Every original successive coordinate has its explicit value after elimination. -/
@[simp] theorem scaleOneToModification_coord (i : Fin 3) :
    scaleOneToModification W π b3 b4 b6 (coord W 1 π b3 b4 b6 i) = ![t', v', x'] i :=
  evaluation_coord _ _ _ _ _ _ _ _ _ i

/-- The original two-variable algebra recovers the full successive chart. -/
def scaleOneFromModification : B →ₐ[R] A :=
  WeierstrassModificationX.evaluation W π b3 b4 b6 t v (by
    rw [scaleOne_horizontal]
    exact incidence W 1 π b3 b4 b6)

/-- Recovery retains the original incidence ratio. -/
@[simp] theorem scaleOneFromModification_t : scaleOneFromModification W π b3 b4 b6 t' = t :=
  WeierstrassModificationX.evaluation_t _ _ _ _ _ _ _ _

/-- Recovery retains the original tangent slope. -/
@[simp] theorem scaleOneFromModification_v : scaleOneFromModification W π b3 b4 b6 v' = v :=
  WeierstrassModificationX.evaluation_v _ _ _ _ _ _ _ _

/-- Recovery retains the original horizontal cubic function. -/
@[simp] theorem scaleOneFromModification_x : scaleOneFromModification W π b3 b4 b6 x' = u := by
  simp only [WeierstrassModificationX.x, map_sub, map_add, map_mul, map_pow, AlgHom.commutes,
    scaleOneFromModification_v, scaleOneFromModification_t]
  exact scaleOne_horizontal W π b3 b4 b6

/-- Eliminating and then recovering the third coordinate fixes the whole successive algebra. -/
theorem scaleOneFromModification_to :
    (scaleOneFromModification W π b3 b4 b6).comp (scaleOneToModification W π b3 b4 b6) =
      AlgHom.id R A := by
  apply hom_ext
  intro i
  fin_cases i <;> simp [AlgHom.comp_apply]

/-- Recovering and then eliminating fixes the whole two-variable algebra. -/
theorem scaleOneToModification_from :
    (scaleOneToModification W π b3 b4 b6).comp (scaleOneFromModification W π b3 b4 b6) =
      AlgHom.id R B := by
  apply WeierstrassModificationX.hom_ext <;> simp [AlgHom.comp_apply]

/-- The full scale-one successive chart is the original two-variable modification chart. -/
def scaleOneModificationEquiv : A ≃ₐ[R] B :=
  AlgEquiv.ofAlgHom (scaleOneToModification W π b3 b4 b6)
    (scaleOneFromModification W π b3 b4 b6) (scaleOneToModification_from W π b3 b4 b6)
    (scaleOneFromModification_to W π b3 b4 b6)

/-- The full scale-one comparison retains all three original successive coordinates. -/
theorem scaleOneModificationEquiv_coord (i : Fin 3) :
    scaleOneModificationEquiv W π b3 b4 b6 (coord W 1 π b3 b4 b6 i) = ![t', v', x'] i :=
  scaleOneToModification_coord W π b3 b4 b6 i

end FLT.Mazur.WeierstrassSuccessiveX

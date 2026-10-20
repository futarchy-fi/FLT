/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXAlgebra

/-!
# Integral negation on the entire successive incidence chart

The incidence and horizontal coordinates are fixed, and the slope is sent to
its other quadratic root. Both defining relations hold over any coefficient ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "A" => Coordinate W s π b3 b4 b6
local notation "t" => coord W s π b3 b4 b6 0
local notation "v" => coord W s π b3 b4 b6 1
local notation "u" => coord W s π b3 b4 b6 2

/-- Reflection in the two quadratic roots preserves the full equation. -/
theorem negation_equation :
    (-v - algebraMap R A W.a₁ - algebraMap R A b3 * t) ^ 2 +
        (algebraMap R A W.a₁ + algebraMap R A b3 * t) *
          (-v - algebraMap R A W.a₁ - algebraMap R A b3 * t) =
      algebraMap R A s * u + algebraMap R A W.a₂ +
        algebraMap R A b4 * t + algebraMap R A b6 * t ^ 2 := by
  linear_combination equation W s π b3 b4 b6

/-- The integral negative on the actual three-generator successive chart. -/
def negation : A →ₐ[R] A :=
  evaluation W s π b3 b4 b6
    ![t, -v - algebraMap R A W.a₁ - algebraMap R A b3 * t, u]
    (negation_equation W s π b3 b4 b6) (incidence W s π b3 b4 b6)

/-- The incidence ratio is fixed by negation. -/
@[simp] theorem negation_t : negation W s π b3 b4 b6 t = t :=
  evaluation_coord _ _ _ _ _ _ _ _ _ 0

/-- The full original slope formula, including its divided third coefficient. -/
@[simp] theorem negation_v : negation W s π b3 b4 b6 v =
    -v - algebraMap R A W.a₁ - algebraMap R A b3 * t :=
  evaluation_coord _ _ _ _ _ _ _ _ _ 1

/-- The preceding horizontal coordinate is fixed without cancelling the scale. -/
@[simp] theorem negation_u : negation W s π b3 b4 b6 u = u :=
  evaluation_coord _ _ _ _ _ _ _ _ _ 2

/-- The negative is involutive on the entire coordinate algebra. -/
theorem negation_comp :
    (negation W s π b3 b4 b6).comp (negation W s π b3 b4 b6) = AlgHom.id R A := by
  apply hom_ext
  intro i
  fin_cases i
  · change negation W s π b3 b4 b6 (negation W s π b3 b4 b6 t) = t
    rw [negation_t, negation_t]
  · change negation W s π b3 b4 b6 (negation W s π b3 b4 b6 v) = v
    simp only [negation_v, map_sub, map_neg, map_mul, AlgHom.commutes, negation_t]
    ring
  · change negation W s π b3 b4 b6 (negation W s π b3 b4 b6 u) = u
    rw [negation_u, negation_u]

/-- Negation is an actual automorphism of the whole successive incidence chart. -/
def negationEquiv : A ≃ₐ[R] A :=
  AlgEquiv.ofAlgHom (negation W s π b3 b4 b6) (negation W s π b3 b4 b6)
    (negation_comp W s π b3 b4 b6) (negation_comp W s π b3 b4 b6)

end FLT.Mazur.WeierstrassSuccessiveX

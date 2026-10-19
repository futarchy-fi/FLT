/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationAlgebra

/-!
# Integral negation on every divided chart

The quadratic equation is invariant under the original Weierstrass negative.
This gives an actual involution over the coefficient ring at arbitrary depth,
without inverting the scale or discarding the exceptional fiber.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
local notation "A" => Coordinate W s b3 b4 b6
local notation "u" => x W s b3 b4 b6
local notation "v" => y W s b3 b4 b6

/-- The integral negative satisfies the same entire divided equation. -/
theorem negation_equation :
    (-v - algebraMap R A W.a₁ * u - algebraMap R A b3) ^ 2 +
        (algebraMap R A W.a₁ * u + algebraMap R A b3) *
          (-v - algebraMap R A W.a₁ * u - algebraMap R A b3) =
      algebraMap R A s * u ^ 3 + algebraMap R A W.a₂ * u ^ 2 +
        algebraMap R A b4 * u + algebraMap R A b6 := by
  linear_combination equation W s b3 b4 b6

/-- The actual divided-chart algebra map induced by Weierstrass negation. -/
def negation : A →ₐ[R] A :=
  evaluation W s b3 b4 b6 u (-v - algebraMap R A W.a₁ * u - algebraMap R A b3)
    (negation_equation W s b3 b4 b6)

/-- Negation fixes the divided horizontal coordinate. -/
@[simp] theorem negation_x : negation W s b3 b4 b6 u = u :=
  evaluation_x _ _ _ _ _ _ _ _

/-- Negation retains the full vertical formula and its original divided coefficient. -/
@[simp] theorem negation_y :
    negation W s b3 b4 b6 v = -v - algebraMap R A W.a₁ * u - algebraMap R A b3 :=
  evaluation_y _ _ _ _ _ _ _ _

/-- The actual integral chart map is involutive on all regular functions. -/
theorem negation_comp :
    (negation W s b3 b4 b6).comp (negation W s b3 b4 b6) = AlgHom.id R A := by
  apply hom_ext
  · simp only [AlgHom.comp_apply, negation_x, AlgHom.id_apply]
  · simp only [AlgHom.comp_apply, negation_y, map_sub, map_neg, map_mul,
      AlgHom.commutes, negation_x, AlgHom.id_apply]
    ring

/-- The divided chart has an actual coefficient-preserving negation automorphism. -/
def negationEquiv : A ≃ₐ[R] A :=
  AlgEquiv.ofAlgHom (negation W s b3 b4 b6) (negation W s b3 b4 b6)
    (negation_comp W s b3 b4 b6) (negation_comp W s b3 b4 b6)

/-- The inverse of the divided negation is the same integral morphism. -/
theorem negationEquiv_symm : (negationEquiv W s b3 b4 b6).symm =
    negationEquiv W s b3 b4 b6 := rfl

end FLT.Mazur.WeierstrassDilatation

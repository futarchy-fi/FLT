/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentOverlap

/-!
# Splitting the actual quadratic Cech overlap

When the tangent discriminant is a unit, interpolation in the second root
identifies the original tensor algebra with the product of the identity
and conjugate branches. Both original coefficient projections are retained.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "s" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "σ" => nodeTangentConjugation W

/-- Interpolation in the two separated roots realizes any prescribed pair of branch values. -/
theorem nodeTangentOverlapMap_surjective (hb : IsUnit W.b₂) :
    Function.Surjective (nodeTangentOverlapMap W) := by
  rintro ⟨x, y⟩
  let d : Sˣ := (nodeTangentRoot_derivative_isUnit W hb).unit
  let b : S := (x - y) * (↑d⁻¹ : S)
  let c : S := x - b * s
  have hd : b * (algebraMap R S W.a₁ + 2 * s) = x - y := by
    change ((x - y) * (↑d⁻¹ : S)) * _ = _
    rw [← (nodeTangentRoot_derivative_isUnit W hb).unit_spec, mul_assoc,
      Units.inv_mul, mul_one]
  refine ⟨b ⊗ₜ[R] s + c ⊗ₜ[R] (1 : S), ?_⟩
  rw [map_add, nodeTangentOverlapMap_tmul, nodeTangentOverlapMap_tmul]
  apply Prod.ext
  · change b * s + c * 1 = x
    dsimp only [c]
    ring
  · change b * σ s + c * σ 1 = y
    rw [map_one, mul_one,
      show σ s = -algebraMap R S W.a₁ - s from nodeTangentConjugationHom_root W]
    dsimp only [c]
    linear_combination -hd

/-- The exact quadratic Cech algebra is the product of its two Galois branches. -/
def nodeTangentOverlapEquiv [Nontrivial R] (hb : IsUnit W.b₂) :
    S ⊗[R] S ≃ₐ[R] S × S :=
  AlgEquiv.ofBijective (nodeTangentOverlapMap W)
    ⟨nodeTangentOverlapMap_injective W hb, nodeTangentOverlapMap_surjective W hb⟩

/-- The comparison evaluates every original pure tensor in the two overlap branches. -/
@[simp] theorem nodeTangentOverlapEquiv_tmul [Nontrivial R] (hb : IsUnit W.b₂) (x y : S) :
    nodeTangentOverlapEquiv W hb (x ⊗ₜ[R] y) = (x * y, x * σ y) := rfl

/-- The first original coefficient projection is diagonal on the two branches. -/
theorem nodeTangentOverlapEquiv_first [Nontrivial R] (hb : IsUnit W.b₂) (x : S) :
    nodeTangentOverlapEquiv W hb (x ⊗ₜ[R] (1 : S)) = (x, x) := by simp

/-- The second original projection is identity on one branch and conjugation on the other. -/
theorem nodeTangentOverlapEquiv_second [Nontrivial R] (hb : IsUnit W.b₂) (y : S) :
    nodeTangentOverlapEquiv W hb ((1 : S) ⊗ₜ[R] y) = (y, σ y) := by simp

end FLT.Mazur

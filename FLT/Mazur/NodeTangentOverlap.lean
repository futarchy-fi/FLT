/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentOverlapLinear

/-!
# The two actual branches of the quadratic coefficient overlap

The original Cech algebra maps to the product by multiplication and twisted
multiplication. A unit tangent discriminant makes these branches jointly
injective; no domain or irreducibility assumption on the cover is used.
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

/-- Multiplication on the actual quadratic coefficient overlap. -/
def nodeTangentOverlapIdentity : S ⊗[R] S →ₐ[R] S :=
  Algebra.TensorProduct.lift (AlgHom.id R S) (AlgHom.id R S) (fun _ _ => Commute.all _ _)

/-- The conjugate branch keeps the first coefficient and conjugates the second. -/
def nodeTangentOverlapConjugate : S ⊗[R] S →ₐ[R] S :=
  Algebra.TensorProduct.lift (AlgHom.id R S) (σ).toAlgHom (fun _ _ => Commute.all _ _)

@[simp] theorem nodeTangentOverlapIdentity_tmul (x y : S) :
    nodeTangentOverlapIdentity W (x ⊗ₜ[R] y) = x * y := rfl

@[simp] theorem nodeTangentOverlapConjugate_tmul (x y : S) :
    nodeTangentOverlapConjugate W (x ⊗ₜ[R] y) = x * σ y := rfl

/-- The comparison from the original Cech tensor algebra to its two branches. -/
def nodeTangentOverlapMap : S ⊗[R] S →ₐ[R] S × S :=
  (nodeTangentOverlapIdentity W).prod (nodeTangentOverlapConjugate W)

@[simp] theorem nodeTangentOverlapMap_tmul (x y : S) :
    nodeTangentOverlapMap W (x ⊗ₜ[R] y) = (x * y, x * σ y) := rfl

/-- The unit transverse derivative separates the two actual overlap branches. -/
theorem nodeTangentOverlapMap_injective [Nontrivial R] (hb : IsUnit W.b₂) :
    Function.Injective (nodeTangentOverlapMap W) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨b, c, rfl⟩ := nodeTangentOverlap_exists_linear W z
  have h₁ := congrArg Prod.fst hz
  have h₂ := congrArg Prod.snd hz
  simp only [map_add, nodeTangentOverlapMap_tmul, Prod.fst_add, Prod.snd_add,
    map_one, mul_one, Prod.fst_zero, Prod.snd_zero] at h₁ h₂
  have hr : σ s = -algebraMap R S W.a₁ - s := nodeTangentConjugationHom_root W
  rw [hr] at h₂
  have hd : b * (algebraMap R S W.a₁ + 2 * s) = 0 := by linear_combination h₁ - h₂
  have hb0 : b = 0 := (nodeTangentRoot_derivative_isUnit W hb).mul_left_eq_zero.mp hd
  have hc0 : c = 0 := by simpa only [hb0, zero_mul, zero_add] using h₁
  simp only [hb0, hc0, TensorProduct.zero_tmul, add_zero]

end FLT.Mazur

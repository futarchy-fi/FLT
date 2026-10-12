/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentAlgebra
public import FLT.Mazur.TensorCoefficientSymmetry

/-!
# Tangent conjugation on the original tensor-coordinate functions

Keep both original coordinates fixed and exchange the two adjoined tangent
roots. The two tangent factors are exchanged by the actual tensor
coefficient operation. Wherever they are units, their ratio is inverted.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur
set_option backward.isDefEq.respectTransparency false
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (W : WeierstrassCurve R)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "s" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "e" => TensorCoefficientSymmetry.equiv (A := A) (nodeTangentConjugation W)

/-- The actual tensor coefficient operation squares to the identity on every chart function. -/
theorem nodeTangentTensorConjugation_involutive : Function.Involutive e := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [TensorCoefficientSymmetry.equiv_tmul]
    rw [show nodeTangentConjugation W (nodeTangentConjugation W a) = a from
      nodeTangentConjugationHom_involutive W a]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The first tangent factor in the original, unsheared chart coordinates. -/
def nodeTangentTensorFirst (x y : A) : S ⊗[R] A := 1 ⊗ₜ[R] y - s ⊗ₜ[R] x

/-- The second tangent factor in the same original chart coordinates. -/
def nodeTangentTensorSecond (x y : A) : S ⊗[R] A :=
  1 ⊗ₜ[R] y + (algebraMap R S W.a₁ + s) ⊗ₜ[R] x

/-- Actual coefficient conjugation exchanges the first tangent factor with the second. -/
theorem nodeTangentTensorFirst_conjugate (x y : A) :
    e (nodeTangentTensorFirst W x y) = nodeTangentTensorSecond W x y := by
  simp only [nodeTangentTensorFirst, nodeTangentTensorSecond, map_sub,
    TensorCoefficientSymmetry.equiv_tmul, map_one]
  rw [show nodeTangentConjugation W s = -algebraMap R S W.a₁ - s from
    nodeTangentConjugationHom_root W]
  rw [show -algebraMap R S W.a₁ - s = -(algebraMap R S W.a₁ + s) by ring,
    TensorProduct.neg_tmul, sub_neg_eq_add]

/-- The other tangent factor returns to the first under the same coefficient operation. -/
theorem nodeTangentTensorSecond_conjugate (x y : A) :
    e (nodeTangentTensorSecond W x y) = nodeTangentTensorFirst W x y := by
  simp only [nodeTangentTensorFirst, nodeTangentTensorSecond, map_add,
    TensorCoefficientSymmetry.equiv_tmul, map_one, AlgEquiv.commutes]
  rw [show nodeTangentConjugation W s = -algebraMap R S W.a₁ - s from
    nodeTangentConjugationHom_root W]
  rw [show algebraMap R S W.a₁ + (-algebraMap R S W.a₁ - s) = -s by ring,
    TensorProduct.neg_tmul, ← sub_eq_add_neg]

/-- The product of the original tangent factors is fixed, so its principal open is stable. -/
theorem nodeTangentTensorProduct_conjugate (x y : A) :
    e (nodeTangentTensorFirst W x y * nodeTangentTensorSecond W x y) =
      nodeTangentTensorFirst W x y * nodeTangentTensorSecond W x y := by
  rw [map_mul, nodeTangentTensorFirst_conjugate, nodeTangentTensorSecond_conjugate, mul_comm]

/-- The actual unit-valued tangent ratio has inverse orientation under coefficient conjugation. -/
theorem nodeTangentTensorRatio_conjugate (x y : A) (u v : (S ⊗[R] A)ˣ)
    (hu : (u : S ⊗[R] A) = nodeTangentTensorFirst W x y)
    (hv : (v : S ⊗[R] A) = nodeTangentTensorSecond W x y) :
    Units.map (e).toAlgHom.toMonoidHom (u * v⁻¹) = (u * v⁻¹)⁻¹ := by
  have h1 : Units.map (e).toAlgHom.toMonoidHom u = v := by
    apply Units.ext
    change e (u : S ⊗[R] A) = (v : S ⊗[R] A)
    rw [hu, hv, nodeTangentTensorFirst_conjugate]
  have h2 : Units.map (e).toAlgHom.toMonoidHom v = u := by
    apply Units.ext
    change e (v : S ⊗[R] A) = (u : S ⊗[R] A)
    rw [hu, hv, nodeTangentTensorSecond_conjugate]
  rw [map_mul, map_inv, h1, h2, mul_inv_rev, inv_inv]

end FLT.Mazur

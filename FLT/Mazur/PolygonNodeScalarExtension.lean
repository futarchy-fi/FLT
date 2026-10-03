/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodeScaling
public import Mathlib.RingTheory.TensorProduct.Basic
/-!
# Scalar extension of the node algebra

The coefficient comparison is an algebra equivalence for every commutative
base algebra. Its inverse reconstructs a node function from the two branches
and their common constant. No flatness or preservation of ring pullbacks is
assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped TensorProduct
namespace FLT.Mazur.PolygonNodeScalarExtension
open PolygonNodeEqualizer PolygonNodeLocalization
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
/-- Coefficient extension on both branches, respecting base scalars. -/
def coeffMap : A (R := R) →ₐ[R] A (R := S) where
  __ := PolygonNodeScaling.map (algebraMap R S)
  commutes' r := by
    apply Subtype.ext
    change (Polynomial.map (algebraMap R S) (C r), Polynomial.map (algebraMap R S) (C r)) =
      (C (algebraMap R S r), C (algebraMap R S r))
    simp

/-- The canonical scalar-extension comparison. -/
def comparison : S ⊗[R] A (R := R) →ₐ[S] A (R := S) :=
  AlgHom.liftEquiv R S _ _ coeffMap

@[simp] theorem comparison_tmul (s : S) (p : A (R := R)) :
    comparison (s ⊗ₜ[R] p) = s • PolygonNodeScaling.map (algebraMap R S) p := rfl

@[simp] theorem coeffMap_x : coeffMap (R := R) (S := S) x = x := by
  apply Subtype.ext
  simp [coeffMap, PolygonNodeScaling.map, x]
@[simp] theorem coeffMap_y : coeffMap (R := R) (S := S) y = y := by
  apply Subtype.ext
  simp [coeffMap, PolygonNodeScaling.map, y]

/-- Reconstruct a node function from its branches and common constant. -/
theorem reconstruct (p : A (R := R)) :
    aeval x (first p) + aeval y (second p) -
      algebraMap R (A (R := R)) ((first p).eval 0) = p := by
  have hp : (first p).eval 0 = (second p).eval 0 := p.property
  apply Subtype.ext
  apply Prod.ext
  · change first (aeval x (first p) + aeval y (second p) -
      algebraMap R (A (R := R)) ((first p).eval 0)) = first p
    simp [aeval_def, coeff_zero_eq_eval_zero, hp]
  · change second (aeval x (first p) + aeval y (second p) -
      algebraMap R (A (R := R)) ((first p).eval 0)) = second p
    simp [aeval_def, coeff_zero_eq_eval_zero, add_sub_cancel_left]

/-- The explicit linear inverse to the scalar-extension comparison. -/
def inverseLinear : A (R := S) →ₗ[S] S ⊗[R] A (R := R) :=
  (aeval (1 ⊗ₜ[R] x)).toLinearMap.comp first.toLinearMap +
  (aeval (1 ⊗ₜ[R] y)).toLinearMap.comp second.toLinearMap -
  (Algebra.linearMap S _).comp ((aeval (0 : S)).toLinearMap.comp first.toLinearMap)

theorem inverseLinear_apply (p : A (R := S)) :
    inverseLinear (R := R) p = aeval (1 ⊗ₜ[R] x) (first p) +
      aeval (1 ⊗ₜ[R] y) (second p) - algebraMap S _ ((first p).eval 0) := rfl

theorem comparison_inverse (p : A (R := S)) :
    comparison (inverseLinear (R := R) p) = p := by
  rw [inverseLinear_apply, map_sub, map_add, ← aeval_algHom_apply,
    ← aeval_algHom_apply, AlgHom.commutes]
  have hx : comparison (1 ⊗ₜ[R] x) = (x (R := S)) := by
    change (1 : S) • coeffMap (R := R) (S := S) x = _
    rw [one_smul, coeffMap_x]
  have hy : comparison (1 ⊗ₜ[R] y) = (y (R := S)) := by
    change (1 : S) • coeffMap (R := R) (S := S) y = _
    rw [one_smul, coeffMap_y]
  rw [hx, hy]
  exact reconstruct p

theorem inverse_coeffMap (p : A (R := R)) :
    inverseLinear (coeffMap (S := S) p) = 1 ⊗ₜ[R] p := by
  let i : A (R := R) →ₐ[R] S ⊗[R] A (R := R) := Algebra.TensorProduct.includeRight
  have he (q : R[X]) (z : A (R := R)) :
      aeval (1 ⊗ₜ[R] z) (q.map (algebraMap R S)) = i (aeval z q) := by
    symm
    apply map_aeval_eq_aeval_map
    ext r
    simp [i, IsScalarTower.algebraMap_apply R S (S ⊗[R] A (R := R))]
  rw [inverseLinear_apply]
  change aeval (1 ⊗ₜ[R] x) ((first p).map (algebraMap R S)) +
    aeval (1 ⊗ₜ[R] y) ((second p).map (algebraMap R S)) -
      algebraMap S _ (((first p).map (algebraMap R S)).eval 0) = _
  rw [he, he]
  have hc : algebraMap S (S ⊗[R] A (R := R))
      (((first p).map (algebraMap R S)).eval 0) =
      i (algebraMap R _ ((first p).eval 0)) := by
    simp [i, aeval_def, coeff_zero_eq_eval_zero]
  rw [hc, ← map_add, ← map_sub, reconstruct]
  rfl

theorem inverse_comparison (t : S ⊗[R] A (R := R)) :
    inverseLinear (comparison t) = t := by
  induction t using TensorProduct.inductionOn with
  | tmul s p =>
    change inverseLinear (R := R) (s • coeffMap (R := R) (S := S) p) = _
    rw [map_smul, inverse_coeffMap]
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add a b ha hb => simp [ha, hb]

/-- Node formation commutes with arbitrary extension of coefficients. -/
def nodeTensorIso : S ⊗[R] A (R := R) ≃ₐ[S] A (R := S) :=
  AlgEquiv.ofBijective comparison
    ⟨Function.LeftInverse.injective inverse_comparison,
      Function.RightInverse.surjective comparison_inverse⟩
@[simp]
theorem nodeTensorIso_tmul (s : S) (p : A (R := R)) :
    nodeTensorIso (s ⊗ₜ[R] p) = s • PolygonNodeScaling.map (algebraMap R S) p := rfl

/-- The first branch comparison is polynomial coefficient extension. -/
theorem first_nodeTensorIso_tmul (s : S) (p : A (R := R)) :
    first (nodeTensorIso (s ⊗ₜ[R] p)) = s • (first p).map (algebraMap R S) := by
  rw [nodeTensorIso_tmul, map_smul, PolygonNodeScaling.first_map]

/-- The second branch comparison is polynomial coefficient extension. -/
theorem second_nodeTensorIso_tmul (s : S) (p : A (R := R)) :
    second (nodeTensorIso (s ⊗ₜ[R] p)) = s • (second p).map (algebraMap R S) := by
  rw [nodeTensorIso_tmul, map_smul, PolygonNodeScaling.second_map]

/-- The inverse equivalence is the displayed linear reconstruction. -/
theorem nodeTensorIso_symm_apply (p : A (R := S)) :
    (nodeTensorIso (R := R)).symm p = inverseLinear p := by
  apply (nodeTensorIso (R := R) (S := S)).injective
  exact (AlgEquiv.apply_symm_apply _ p).trans (comparison_inverse p).symm

end FLT.Mazur.PolygonNodeScalarExtension

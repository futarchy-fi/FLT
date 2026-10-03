/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodePresentation
public import Mathlib.RingTheory.PolynomialAlgebra
/-!
# Scalar extension of the one-gon algebra

A split linear retraction of the polynomial normalization proves that formation
of the endpoint equalizer commutes with arbitrary coefficient extension.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped TensorProduct
namespace FLT.Mazur.OneGonScalarExtension
open PolygonNodePresentation
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
/-- Coefficient extension preserving the endpoint equalizer. -/
def coeffMap : B (R := R) →ₐ[R] B (R := S) where
  toFun p := ⟨p.val.map (algebraMap R S), by
    rw [mem_B]
    simpa only [eval_map, ← map_zero (algebraMap R S), ← map_one (algebraMap R S),
      eval₂_at_apply] using congrArg (algebraMap R S) ((mem_B _).mp p.property)⟩
  map_one' := Subtype.ext (Polynomial.map_one _)
  map_mul' p q := Subtype.ext (Polynomial.map_mul _)
  map_zero' := Subtype.ext (Polynomial.map_zero _)
  map_add' p q := Subtype.ext (Polynomial.map_add _)
  commutes' r := Subtype.ext (Polynomial.map_C _)
/-- The canonical scalar-extension comparison. -/
def comparison : S ⊗[R] B (R := R) →ₐ[S] B (R := S) :=
  AlgHom.liftEquiv R S _ _ coeffMap
@[simp] theorem comparison_tmul (s : S) (p : B (R := R)) :
    comparison (s ⊗ₜ[R] p) = s • coeffMap p := rfl

/-- A linear retraction onto polynomials with equal endpoint values. -/
def retract : R[X] →ₗ[R] B (R := R) where
  toFun p := ⟨p - C (p.eval 1 - p.eval 0) * X, by simp⟩
  map_add' p q := by
    apply Subtype.ext
    simp only [eval_add, C_sub, C_add, Subalgebra.coe_add]
    ring
  map_smul' r p := by
    apply Subtype.ext
    simp only [eval_smul, smul_eq_mul, RingHom.id_apply, Subalgebra.coe_smul]
    simp only [mul_sub, map_sub, map_mul, smul_eq_C_mul]
    ring
@[simp] theorem retract_val (p : B (R := R)) : retract p.val = p := by
  apply Subtype.ext
  change p.val - C (p.val.eval 1 - p.val.eval 0) * X = p.val
  rw [← (mem_B _).mp p.property]
  simp

theorem retract_map (p : R[X]) :
    retract (p.map (algebraMap R S)) = coeffMap (retract p) := by
  apply Subtype.ext
  change p.map (algebraMap R S) -
    C ((p.map (algebraMap R S)).eval 1 - (p.map (algebraMap R S)).eval 0) * X =
    (p - C (p.eval 1 - p.eval 0) * X).map (algebraMap R S)
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    eval_map, ← map_zero (algebraMap R S), ← map_one (algebraMap R S), eval₂_at_apply,
    map_sub]

/-- The normalization inclusion after tensoring. -/
def normalizationLinear : S ⊗[R] B (R := R) →ₗ[R] S ⊗[R] R[X] :=
  TensorProduct.map (LinearMap.id : S →ₗ[R] S) (B (R := R)).val.toLinearMap

/-- Tensor the linear retraction of the normalization. -/
def retractTensor : S ⊗[R] R[X] →ₗ[R] S ⊗[R] B (R := R) :=
  TensorProduct.map (LinearMap.id : S →ₗ[R] S) retract

theorem retractTensor_normalization (t : S ⊗[R] B (R := R)) :
    retractTensor (normalizationLinear t) = t := by
  induction t using TensorProduct.inductionOn with
  | tmul s p => simp [retractTensor, normalizationLinear]
  | add a b ha hb => simp [ha, hb]

theorem normalization_comparison (t : S ⊗[R] B (R := R)) :
    (comparison t).val = (polyEquivTensor R S).symm (normalizationLinear t) := by
  induction t using TensorProduct.inductionOn with
  | tmul s p => rfl
  | add a b ha hb => simp [ha, hb]

theorem comparison_injective : Function.Injective (comparison (R := R) (S := S)) := by
  intro x y h
  have hn : normalizationLinear x = normalizationLinear y := by
    apply (polyEquivTensor R S).symm.injective
    rw [← normalization_comparison, ← normalization_comparison, h]
  simpa only [retractTensor_normalization] using congrArg retractTensor hn

theorem comparison_retractTensor (t : S ⊗[R] R[X]) :
    comparison (retractTensor t) = retract ((polyEquivTensor R S).symm t) := by
  induction t using TensorProduct.inductionOn with
  | tmul s p =>
    change s • coeffMap (retract p) = retract (s • p.map (algebraMap R S))
    rw [map_smul, retract_map]
  | add a b ha hb => simp [ha, hb]

theorem comparison_surjective : Function.Surjective (comparison (R := R) (S := S)) := by
  intro p
  refine ⟨retractTensor (polyEquivTensor R S p.val), ?_⟩
  rw [comparison_retractTensor, AlgEquiv.symm_apply_apply, retract_val]

/-- One-gon formation commutes with arbitrary coefficient extension. -/
def oneGonTensorIso : S ⊗[R] B (R := R) ≃ₐ[S] B (R := S) :=
  AlgEquiv.ofBijective comparison ⟨comparison_injective, comparison_surjective⟩

@[simp] theorem oneGonTensorIso_tmul (s : S) (p : B (R := R)) :
    oneGonTensorIso (s ⊗ₜ[R] p) = s • coeffMap p := rfl

theorem normalization_oneGonTensorIso (t : S ⊗[R] B (R := R)) :
    (oneGonTensorIso t).val = (polyEquivTensor R S).symm (normalizationLinear t) :=
  normalization_comparison t

theorem bEval_oneGonTensorIso_tmul (s : S) (p : B (R := R)) :
    bEval (oneGonTensorIso (s ⊗ₜ[R] p)) = s * algebraMap R S (bEval p) := by
  change (s • p.val.map (algebraMap R S)).eval 0 = _
  simp [bEval, aeval_def, coeff_zero_eq_eval_zero]
/-- The second endpoint has the same coefficient-extension formula. -/
theorem eval_one_oneGonTensorIso_tmul (s : S) (p : B (R := R)) :
    (oneGonTensorIso (s ⊗ₜ[R] p)).val.eval 1 = s * algebraMap R S (bEval p) := by
  rw [← (mem_B _).mp (oneGonTensorIso (s ⊗ₜ[R] p)).property]
  exact bEval_oneGonTensorIso_tmul s p
end FLT.Mazur.OneGonScalarExtension

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassChangeCoefficientBaseChange
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The actual comparison algebra commutes with coefficient base change

The five-equation comparison algebra after scalar extension is isomorphic
to the tensor product of the original algebra. This follows from its full,
natural parameter classification and imposes no flatness assumption.
-/

@[expose] public noncomputable section
open WeierstrassCurve
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassChangeParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
  (W V : WeierstrassCurve R)
local notation "Q" => EquationRing W V
local notation "Q'" => EquationRing (W.map (algebraMap R A)) (V.map (algebraMap R A))
local notation "T" => A ⊗[R] Q

/-- The tensor-product and changed-coefficient algebras represent the same full comparisons. -/
def tensorParameterEquiv (B : Type) [CommRing B] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B] :
    (Q' →ₐ[A] B) ≃ (T →ₐ[A] B) :=
  (coefficientParameterEquiv W V).trans (AlgHom.liftEquiv R A Q B)

/-- This algebra identification on tests commutes with every map of test algebras. -/
theorem tensorParameterEquiv_natural {B D : Type} [CommRing B] [CommRing D]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A D] [Algebra R D] [IsScalarTower R A D]
    (f : Q' →ₐ[A] B) (g : B →ₐ[A] D) :
    tensorParameterEquiv W V D (g.comp f) = g.comp (tensorParameterEquiv W V B f) := by
  unfold tensorParameterEquiv
  change (AlgHom.liftEquiv R A Q D) (coefficientParameterEquiv W V (g.comp f)) = _
  rw [coefficientParameterEquiv_natural]
  apply Algebra.TensorProduct.ext_ring
  ext x
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.includeRight_apply, Equiv.trans_apply,
    AlgHom.liftEquiv_tmul, one_smul]

/-- The forward map is obtained by evaluating the universal comparison after base change. -/
def coefficientTensorForward : T →ₐ[A] Q' :=
  tensorParameterEquiv W V Q' (AlgHom.id A Q')

/-- The inverse is obtained by the original universal comparison on the tensor product. -/
def coefficientTensorInverse : Q' →ₐ[A] T :=
  (tensorParameterEquiv W V T).symm (AlgHom.id A T)

/-- The two universal maps recover every changed-coefficient coordinate. -/
theorem coefficientTensor_forward_inverse :
    (coefficientTensorForward W V).comp (coefficientTensorInverse W V) = AlgHom.id A Q' := by
  apply (tensorParameterEquiv W V Q').injective
  rw [tensorParameterEquiv_natural (A := A) (B := T) (D := Q')]
  change (coefficientTensorForward W V).comp
    ((tensorParameterEquiv W V T) ((tensorParameterEquiv W V T).symm (AlgHom.id A T))) = _
  rw [Equiv.apply_symm_apply, AlgHom.comp_id]
  rfl

/-- The two universal maps also recover every original tensor-product coordinate. -/
theorem coefficientTensor_inverse_forward :
    (coefficientTensorInverse W V).comp (coefficientTensorForward W V) = AlgHom.id A T := by
  have h := tensorParameterEquiv_natural (A := A) (B := Q') (D := T) W V
    (AlgHom.id A Q') (coefficientTensorInverse (A := A) W V)
  rw [AlgHom.comp_id] at h
  change (tensorParameterEquiv W V T)
    ((tensorParameterEquiv W V T).symm (AlgHom.id A T)) = _ at h
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- Full comparison algebras commute with arbitrary coefficient base change. -/
def coefficientTensorEquiv : T ≃ₐ[A] Q' :=
  AlgEquiv.ofAlgHom (coefficientTensorForward W V) (coefficientTensorInverse W V)
    (coefficientTensor_forward_inverse W V) (coefficientTensor_inverse_forward W V)

end FLT.Mazur.WeierstrassChangeParameter

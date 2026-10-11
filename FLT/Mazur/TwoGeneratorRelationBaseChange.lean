/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TwoGeneratorRelationQuotient
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Base change of the explicit one-relation quotient

Extending coefficients commutes with the two-generator presentation, with
formulas retaining both original generators.
-/

@[expose] public noncomputable section

open TensorProduct

namespace FLT.Mazur.TwoGeneratorRelation

variable {C : Type*} [CommRing C] (x y : C) (S : Type*) [CommRing S] [Algebra C S]

/-- The original quotient maps linearly to the quotient with extended coefficients. -/
def scalarMap : Model x y →ₗ[C] Model (algebraMap C S x) (algebraMap C S y) :=
  lift x y (left _ _) (right _ _) (by
    rw [← algebraMap_smul S x, ← algebraMap_smul S y]
    exact relation _ _)

/-- Extension of scalars maps to the explicit extended-coefficient quotient. -/
def baseChangeMap : S ⊗[C] Model x y →ₗ[S]
    Model (algebraMap C S x) (algebraMap C S y) :=
  AlgebraTensorModule.lift ((LinearMap.id (R := S)).smulRight (scalarMap x y S))

/-- The base-change map is scalar extension of the original quotient map. -/
@[simp] theorem baseChangeMap_tmul (a : S) (q : Model x y) :
    baseChangeMap x y S (a ⊗ₜ[C] q) = a • scalarMap x y S q := rfl

/-- The extended relation holds on the original generators in the tensor product. -/
theorem tensor_relation :
    algebraMap C S x • ((1 : S) ⊗ₜ[C] right x y) +
      algebraMap C S y • ((1 : S) ⊗ₜ[C] left x y) = 0 := by
  have h := congrArg (fun q : Model x y ↦ (1 : S) ⊗ₜ[C] q) (relation x y)
  simpa only [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_zero,
    algebraMap_smul] using h

/-- The explicit extended quotient maps back to the tensor product. -/
def baseChangeInverse : Model (algebraMap C S x) (algebraMap C S y) →ₗ[S]
    S ⊗[C] Model x y :=
  lift _ _ ((1 : S) ⊗ₜ[C] left x y) ((1 : S) ⊗ₜ[C] right x y) (tensor_relation x y S)

/-- The inverse comparison recovers a pure tensor with coefficient one. -/
theorem baseChangeInverse_scalarMap (q : Model x y) :
    baseChangeInverse x y S (scalarMap x y S q) = (1 : S) ⊗ₜ[C] q := by
  have h : ((baseChangeInverse x y S).restrictScalars C).comp (scalarMap x y S) =
      TensorProduct.mk C S (Model x y) 1 := by
    apply hom_ext
    · simp [LinearMap.comp_apply, scalarMap, baseChangeInverse]
    · simp [LinearMap.comp_apply, scalarMap, baseChangeInverse]
  exact LinearMap.congr_fun h q

/-- Both comparisons compose to identity on the tensor product. -/
theorem baseChangeInverse_map :
    (baseChangeInverse x y S).comp (baseChangeMap x y S) = LinearMap.id := by
  apply AlgebraTensorModule.ext
  intro a q
  change baseChangeInverse x y S (baseChangeMap x y S (a ⊗ₜ[C] q)) = a ⊗ₜ[C] q
  rw [baseChangeMap_tmul, map_smul, baseChangeInverse_scalarMap, TensorProduct.smul_tmul']
  simp

/-- Both comparisons compose to identity on the extended quotient. -/
theorem baseChangeMap_inverse :
    (baseChangeMap x y S).comp (baseChangeInverse x y S) = LinearMap.id := by
  apply hom_ext
  · simp [LinearMap.comp_apply, baseChangeInverse, scalarMap]
  · simp [LinearMap.comp_apply, baseChangeInverse, scalarMap]

/-- Scalar extension commutes with the explicit two-generator one-relation quotient. -/
def baseChangeEquiv : S ⊗[C] Model x y ≃ₗ[S]
    Model (algebraMap C S x) (algebraMap C S y) :=
  { baseChangeMap x y S with
    invFun := baseChangeInverse x y S
    left_inv := LinearMap.congr_fun (baseChangeInverse_map x y S)
    right_inv := LinearMap.congr_fun (baseChangeMap_inverse x y S) }

end FLT.Mazur.TwoGeneratorRelation

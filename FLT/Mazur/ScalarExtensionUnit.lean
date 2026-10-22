/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealTensorCoefficientTransition
public import FLT.Mazur.ResidualKernelSpan

/-!
# Semilinear units of scalar extension

The unit of module scalar extension is compatible with presentation maps.
For quotient coefficients the actual semilinear tensor transition agrees
with the generator obtained by cancelling scalar extensions.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ScalarExtensionUnit
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  (P : Type*) [AddCommGroup P] [Module R P]

/-- The canonical unit of scalar extension, retaining its semilinearity. -/
def unit : P →ₛₗ[algebraMap R S] S ⊗[R] P where
  toFun x := 1 ⊗ₜ[R] x
  map_add' x y := tmul_add _ _ _
  map_smul' r x := by
    rw [tmul_smul, ← algebraMap_smul S r, smul_tmul', smul_eq_mul, mul_one]

@[simp]
theorem unit_apply (x : P) : unit S P x = 1 ⊗ₜ[R] x := rfl

variable {P} {N : Type*} [AddCommGroup N] [Module R N]

/-- The unit commutes with every presentation differential. -/
theorem differential (f : P →ₗ[R] N) (x : P) :
    f.baseChange S (unit S P x) = unit S N (f x) := rfl

variable (I : Ideal R)

/-- The coefficient algebra for the quotient by the actual extended ideal. -/
abbrev quotientAlgebra : Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

attribute [local instance] quotientAlgebra

/-- The quotient coefficient algebra is compatible with the original base ring. -/
theorem quotientTower : IsScalarTower R (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

attribute [local instance] quotientTower

/-- Cancelling the new scalar extension computes the original relation generator. -/
theorem quotient_cancel (z : (R ⧸ I) ⊗[R] P) :
    AlgebraTensorModule.cancelBaseChange R S (S ⧸ I.map (algebraMap R S))
      (S ⧸ I.map (algebraMap R S)) P
      (TensorProduct.map (IdealTensorCoefficientTransition.quotientTransition
        (algebraMap R S) I) (unit S P) z) =
    AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (S ⧸ I.map (algebraMap R S))
      (S ⧸ I.map (algebraMap R S)) P (1 ⊗ₜ[R ⧸ I] z) := by
  induction z with
  | tmul a x =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    simp only [TensorProduct.map_tmul, unit_apply,
      IdealTensorCoefficientTransition.quotientTransition_mk,
      AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def, mul_one, map_one, one_mul]
    rfl
  | add x y hx hy => simp only [map_add, tmul_add, hx, hy]

end FLT.Mazur.ScalarExtensionUnit

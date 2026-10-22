/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarExtensionUnit

/-!
# Residual flatness after the same scalar extension

Quotienting the new base by the actual extended ideal and tensoring the
extended module agrees with base change of the original residual module.
Thus its flatness follows without flatness of the base transition itself.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.IdealResidualFlatBaseChange
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (S : Type*) [CommRing S] [Algebra R S] (I : Ideal R)

attribute [local instance] ScalarExtensionUnit.quotientAlgebra
  ScalarExtensionUnit.quotientTower

/-- Compare the actual new residual module with scalar extension of the old residual module. -/
def residualEquiv :
    (S ⧸ I.map (algebraMap R S)) ⊗[S] (S ⊗[R] M) ≃ₗ[S ⧸ I.map (algebraMap R S)]
      (S ⧸ I.map (algebraMap R S)) ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] M) :=
  (AlgebraTensorModule.cancelBaseChange R S (S ⧸ I.map (algebraMap R S))
    (S ⧸ I.map (algebraMap R S)) M).trans
    (AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (S ⧸ I.map (algebraMap R S))
      (S ⧸ I.map (algebraMap R S)) M).symm

/-- Residual flatness is preserved by arbitrary base change with the actual extended ideal. -/
theorem flat [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)] :
    Module.Flat (S ⧸ I.map (algebraMap R S))
      ((S ⧸ I.map (algebraMap R S)) ⊗[S] (S ⊗[R] M)) :=
  Module.Flat.of_linearEquiv (residualEquiv (M := M) S I)

end FLT.Mazur.IdealResidualFlatBaseChange

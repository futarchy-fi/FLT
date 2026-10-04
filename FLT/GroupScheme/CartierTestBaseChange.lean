/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierTestCoefficients

/-! # Scalar extension preserves the actual integral Cartier character -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace HopfAlgebra.CartierDual
variable {R A K S : Type} [CommRing R] [CommRing A] [CommRing K] [CommRing S]
  [Algebra R K] [Algebra R S] [Algebra K S] [IsScalarTower R K S]
  [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]

/-- Base change takes the original dual basis to the dual of the base-changed basis. -/
theorem baseChangeAlgEquiv_coord {ι : Type}
    (b : Module.Basis ι R A) (i : ι) :
    baseChangeAlgEquiv K (1 ⊗ₜ[R] WithConv.toConv (b.coord i)) =
      WithConv.toConv ((b.baseChange K).coord i) := by
  apply WithConv.ext
  apply (TensorProduct.isBaseChange R A K).algHom_ext
  intro a
  change baseChangeAlgEquiv K (1 ⊗ₜ[R] WithConv.toConv (b.coord i)) (1 ⊗ₜ a) = _
  rw [baseChangeAlgEquiv_tmul]
  change _ = (b.baseChange K).repr (1 ⊗ₜ a) i
  simp [Module.Basis.baseChange_repr_tmul, Algebra.smul_def]

/-- Restrict the actual scalar-extended dual point to its original integral coordinates. -/
def testDualRestriction (ψ : CartierDual K (K ⊗[R] A) →ₐ[K] S) :
    CartierDual R A →ₐ[R] S :=
  (ψ.comp (baseChangeAlgEquiv K).toAlgHom).restrictScalars R |>.comp
    Algebra.TensorProduct.includeRight

/-- Restriction preserves evaluation of the dual coordinates. -/
@[simp] theorem testDualRestriction_apply
    (ψ : CartierDual K (K ⊗[R] A) →ₐ[K] S) (φ : CartierDual R A) :
    testDualRestriction ψ φ = ψ (baseChangeAlgEquiv K (1 ⊗ₜ φ)) := rfl

/-- The integral character and the scalar-extended character have exactly the same value. -/
theorem testEvaluation_baseChange (ψ : CartierDual K (K ⊗[R] A) →ₐ[K] S)
    (x : K ⊗[R] A →ₐ[K] S) :
    testEvaluation (testDualRestriction ψ)
        ((x.restrictScalars R).comp Algebra.TensorProduct.includeRight).toLinearMap =
      testEvaluation ψ x.toLinearMap := by
  let b := Module.Free.chooseBasis R A
  rw [testEvaluation_eq_sum b, testEvaluation_eq_sum (b.baseChange K)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [testDualRestriction_apply, baseChangeAlgEquiv_coord]
  simp only [Module.Basis.baseChange_apply, AlgHom.toLinearMap_apply,
    AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply]

end HopfAlgebra.CartierDual

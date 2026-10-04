/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierTestAlgebra
public import FLT.GroupScheme.CartierPairingNaturality

/-! # Original morphisms and geometric specialization of integral Cartier characters -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace HopfAlgebra.CartierDual
variable {R A B S : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing S]
  [Algebra R S] [HopfAlgebra R A] [HopfAlgebra R B]
  [Module.Finite R A] [Module.Free R A] [Module.Finite R B] [Module.Free R B]

/-- The canonical tensor may be computed in any finite basis, independently of that choice. -/
theorem testLinearTensor_eq_sum {ι : Type} [Fintype ι]
    (b : Module.Basis ι R A) (d : A →ₗ[R] S) :
    testLinearTensor d = ∑ i, d (b i) ⊗ₜ[R] WithConv.toConv (b.coord i) := by
  apply (baseChangeAlgEquiv (R := R) (A := A) S).injective
  apply WithConv.ext
  apply (TensorProduct.isBaseChange R A S).algHom_ext
  intro a
  change baseChangeAlgEquiv S (testLinearTensor d) (1 ⊗ₜ a) = _
  rw [testLinearTensor_eval]
  conv_lhs => rw [← b.sum_repr a]
  simp only [map_sum, map_smul]
  simp [Algebra.smul_def, mul_comm]

/-- Integral character evaluation is the coordinate pairing in every finite basis. -/
theorem testEvaluation_eq_sum {ι : Type} [Fintype ι] (b : Module.Basis ι R A)
    (ψ : CartierDual R A →ₐ[R] S) (d : A →ₗ[R] S) :
    testEvaluation ψ d = ∑ i, d (b i) * ψ (WithConv.toConv (b.coord i)) := by
  change AlgHom.liftEquiv R S (CartierDual R A) S ψ (testLinearTensor d) = _
  rw [testLinearTensor_eq_sum b]
  simp

/-- Original coordinate maps act on the canonical representing tensor by their transpose. -/
theorem testLinearTensor_naturality (f : A →ₐc[R] B) (d : B →ₗ[R] S) :
    Algebra.TensorProduct.map (AlgHom.id S S) (map f) (testLinearTensor d) =
      testLinearTensor (d.comp f.toLinearMap) := by
  apply (baseChangeAlgEquiv (R := R) (A := A) S).injective
  apply WithConv.ext
  apply (TensorProduct.isBaseChange R A S).algHom_ext
  intro a
  have he (t : S ⊗[R] CartierDual R B) :
      baseChangeAlgEquiv S
        (Algebra.TensorProduct.map (AlgHom.id S S) (map f) t) (1 ⊗ₜ a) =
      baseChangeAlgEquiv S t (1 ⊗ₜ f a) := by
    induction t using TensorProduct.inductionOn with
    | tmul s φ => simp
    | add t u ht hu => simp only [map_add, WithConv.ofConv_add, LinearMap.add_apply, ht, hu]
  exact (he _).trans ((testLinearTensor_eval d (f a)).trans
    (testLinearTensor_eval (d.comp f.toLinearMap) a).symm)

/-- Cartier evaluation pairs each original coordinate map with its actual transpose. -/
theorem testEvaluation_naturality (f : A →ₐc[R] B)
    (ψ : CartierDual R A →ₐ[R] S) (d : B →ₗ[R] S) :
    testEvaluation (ψ.comp (map f)) d = testEvaluation ψ (d.comp f.toLinearMap) := by
  unfold testEvaluation
  simp only [LinearMap.coe_comp, LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply,
    LinearEquiv.coe_coe, Function.comp_apply]
  rw [← testLinearTensor_naturality f d]
  generalize testLinearTensor d = t
  induction t using TensorProduct.inductionOn with
  | tmul s φ => rfl
  | add t u ht hu => simp only [map_add, ht, hu]

section Geometric
variable {K L C : Type} [Field K] [Field L] [Algebra K L] [CommRing C]
  [HopfAlgebra K C] [Coalgebra.IsCocomm K C] [Module.Finite K C]
  [Algebra.Etale K C] [IsSepClosed L]
attribute [local instance] HopfAlgebra.pointsCommGroup

/-- The integral test-algebra character specializes to the original geometric Cartier pairing. -/
theorem testCharacter_eq_geometric (ψ : CartierDual K C →ₐ[K] L) (x : C →ₐ[K] L) :
    testCharacter ψ (WithConv.toConv x) = geometricCharactersEquiv K L C ψ x := by
  apply Units.ext
  rw [testCharacter_coe, testEvaluation_eq_sum (Module.Free.chooseBasis K C),
    geometricCharactersEquiv_eq_sum K L C (Module.Free.chooseBasis K C)]
  rfl
end Geometric
end HopfAlgebra.CartierDual

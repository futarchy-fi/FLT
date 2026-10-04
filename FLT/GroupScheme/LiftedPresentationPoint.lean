/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LiftedPresentationBaseChange

/-! # Point transport preserves the original reduced coefficients -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace Algebra.Presentation
variable {R B C E ι σ : Type*} [CommRing R] [CommRing B] [CommRing C] [CommRing E]
  [Algebra B C] [Algebra C E] [Algebra B E] [IsScalarTower B C E]
  (P : Presentation C E ι σ) (g : σ → MvPolynomial ι B)
  (hg : ∀ i, MvPolynomial.map (algebraMap B C) (g i) = P.relation i)

/-- Surjectivity of the coefficient quotient makes the reduction comparison C-linear. -/
@[simp]
theorem liftedPresentationBaseChangeEquiv_one_tmul
    (hq : Function.Surjective (algebraMap B C)) (c : C) :
    P.liftedPresentationBaseChangeEquiv g hg hq (1 ⊗ₜ[B] c) = algebraMap C E c := by
  obtain ⟨b, rfl⟩ := hq c
  rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rw [← IsScalarTower.algebraMap_apply B C E]
  exact (P.liftedPresentationBaseChangeEquiv g hg hq).commutes b

variable [Algebra R B] [Algebra R C] [IsScalarTower R B C]
  [Algebra R E] [IsScalarTower R B E] [IsScalarTower R C E]

/-- Transport an actual division point and retain its specified composite over C. -/
theorem exists_point_on_lifted_reduction_over_base
    (hq : Function.Surjective (algebraMap B C))
    {A H : Type*} [CommRing A] [CommRing H] [Algebra R A] [Algebra R H]
    (f : A →ₐ[R] H) (x : A →ₐ[R] C) (y : H →ₐ[R] E)
    (hy : y.comp f = (IsScalarTower.toAlgHom R C E).comp x) :
    ∃ z : H →ₐ[R] ((MvPolynomial ι B ⧸ Ideal.span (Set.range g)) ⊗[B] C),
      ((P.liftedPresentationBaseChangeEquiv g hg hq).restrictScalars R).toAlgHom.comp z = y ∧
      z.comp f = (Algebra.TensorProduct.includeRight.restrictScalars R).comp x := by
  obtain ⟨z, hz, hc⟩ := P.exists_point_on_lifted_reduction g hg hq f
    ((IsScalarTower.toAlgHom R C E).comp x) y hy
  refine ⟨z, hz, hc.trans ?_⟩
  ext a
  apply (P.liftedPresentationBaseChangeEquiv g hg hq).injective
  exact (AlgEquiv.apply_symm_apply _ _).trans
    (P.liftedPresentationBaseChangeEquiv_one_tmul g hg hq (x a)).symm

end Algebra.Presentation

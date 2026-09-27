/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.KummerPoints

/-!
# Additive and equivariant comparison of model points

A point bijection compatible with coaddition identifies the Galois module
represented by a finite-flat Hopf algebra.
-/

@[expose] public section

open scoped TensorProduct
universe u
namespace Bialgebra
variable (R K k H X : Type u) [CommRing R] [Field K] [Field k] [CommRing H]
  [Algebra R K] [Algebra K k] [Algebra R k] [IsScalarTower R K k]
  [HopfAlgebra R H] [AddCommGroup X]
/-- An integral point bijection preserving convolution identifies the generic point group. -/
noncomputable def modelPointsAddEquiv (e : X ≃ (H →ₐ[R] k))
    (he : ∀ P Q, (Algebra.TensorProduct.lift (e P) (e Q)
      (fun _ _ ↦ .all _ _)).comp (comulAlgHom R H) = e (P + Q)) :
    Additive (K ⊗[R] H →ₐ[K] k) ≃+ X where
  toEquiv := (Equiv.refl _).trans ((restrictPoints R K k H).trans e.symm)
  map_add' f g := by
    change e.symm (restrictPoints R K k H (f.toMul * g.toMul)) =
      e.symm (restrictPoints R K k H f.toMul) + e.symm (restrictPoints R K k H g.toMul)
    rw [restrictPoints_mul]
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    rw [← he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

variable [DistribMulAction (k ≃ₐ[K] k) X]
/-- An equivariant integral point bijection exhibits a finite-flat Galois module. -/
theorem isFiniteFlat_of_pointsEquiv [HopfAlgebra.IsFiniteFlat R H]
    [Algebra.Etale K (K ⊗[R] H)] (e : X ≃ (H →ₐ[R] k))
    (he : ∀ P Q, (Algebra.TensorProduct.lift (e P) (e Q)
      (fun _ _ ↦ .all _ _)).comp (comulAlgHom R H) = e (P + Q))
    (hσ : ∀ (σ : k ≃ₐ[K] k) P, e (σ • P) =
      (σ.toAlgHom.restrictScalars R).comp (e P)) :
    GaloisModule.IsFiniteFlat R K k X := by
  let a := modelPointsAddEquiv R K k H X e he
  let f : Additive (K ⊗[R] H →ₐ[K] k) →+[k ≃ₐ[K] k] X :=
    { a.toAddMonoidHom with
      map_smul' := by
        intro σ φ
        apply e.injective
        rw [hσ]
        change e (e.symm _) = (σ.toAlgHom.restrictScalars R).comp (e (e.symm _))
        simp only [Equiv.apply_symm_apply]
        rfl }
  exact ⟨H, inferInstance, inferInstance, inferInstance, inferInstance, f, a.bijective⟩
end Bialgebra

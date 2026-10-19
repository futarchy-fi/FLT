/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlat

/-!
# Geometric scalar extension of equivariant functions

The comparison evaluates every original equivariant function at the same label.
Geometric points detect injectivity, and the finite ranks prove surjectivity.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace GaloisModule

variable (K L X : Type) [Field K] [Field L] [Algebra K L]
  [MulAction (L ≃ₐ[K] L) X]

/-- Scalar extension followed by evaluation at each original label. -/
def scalarExtensionEvaluation :
    L ⊗[K] (X →[L ≃ₐ[K] L] L) →ₐ[L] (X → L) :=
  AlgHom.pi (fun i ↦ Algebra.TensorProduct.liftEquivRight K L _ _
    (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K X L i))

@[simp] theorem scalarExtensionEvaluation_tmul (r : L) (a : X →[L ≃ₐ[K] L] L)
    (i : X) : scalarExtensionEvaluation K L X (r ⊗ₜ[K] a) i = r * a i := rfl

variable [IsGalois K L] [Finite X] [ContinuousSMulDiscrete (L ≃ₐ[K] L) X]

/-- Every geometric point of the scalar extension is the extension of an original evaluation. -/
theorem scalarExtensionEvaluation_points (f : (L ⊗[K] (X →[L ≃ₐ[K] L] L)) →ₐ[L] L) :
    ∃ i : X, f = Algebra.TensorProduct.liftEquivRight K L _ _
      (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K X L i) := by
  obtain ⟨i, hi⟩ := (InfiniteGalois.evalAlgHom_bijective K L X).2
    ((Algebra.TensorProduct.liftEquivRight K L _ _).symm f)
  refine ⟨i, ?_⟩
  rw [hi, Equiv.apply_symm_apply]

variable [IsSepClosed L]

/-- The evaluation comparison is a bijection of algebras, not merely a point bijection. -/
theorem scalarExtensionEvaluation_bijective :
    Function.Bijective (scalarExtensionEvaluation K L X) := by
  let _ := Fintype.ofFinite X
  have hinj : Function.Injective (scalarExtensionEvaluation K L X) := by
    intro a b h
    apply (InfiniteGalois.evalMulActionHom_bijective_of_isSepClosed
      L L (L ⊗[K] (X →[L ≃ₐ[K] L] L))).1
    ext f
    obtain ⟨i, rfl⟩ := scalarExtensionEvaluation_points K L X f
    exact congrFun h i
  have hrank : Module.finrank L (L ⊗[K] (X →[L ≃ₐ[K] L] L)) =
      Module.finrank L (X → L) := by
    rw [Module.finrank_baseChange, finrank_equivariantFunctions K L X,
      Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank
    (f := (scalarExtensionEvaluation K L X).toLinearMap)).mp hinj⟩

/-- Over the separably closed field, the descended algebra is the full product algebra. -/
def scalarExtensionEquiv : L ⊗[K] (X →[L ≃ₐ[K] L] L) ≃ₐ[L] (X → L) :=
  AlgEquiv.ofBijective (scalarExtensionEvaluation K L X)
    (scalarExtensionEvaluation_bijective K L X)

@[simp] theorem scalarExtensionEquiv_tmul (r : L) (a : X →[L ≃ₐ[K] L] L) (i : X) :
    scalarExtensionEquiv K L X (r ⊗ₜ[K] a) i = r * a i := rfl

end GaloisModule

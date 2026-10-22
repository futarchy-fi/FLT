/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarExtensionUnit
public import FLT.Mazur.ScalarPresentationKernel

/-!
# Spanning the actual reduced scalar-extension presentation

The generators are the semilinear quotient transitions of old relations.
Residual flatness and quotient surjectivity prove they generate every new
relation over the new base ring, without injectivity of the first map.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.IdealResidualKernelSpan
open ScalarExtensionUnit
variable {R P N M : Type*} [CommRing R]
  [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
  [AddCommGroup M] [Module R M]
  (S : Type*) [CommRing S] [Algebra R S] (I : Ideal R)

/-- Transport an old reduced relation through the actual quotient and module units. -/
def relation (f : P →ₗ[R] N) : (f.lTensor (R ⧸ I)).ker →ₛₗ[algebraMap R S]
    ((f.baseChange S).lTensor (S ⧸ I.map (algebraMap R S))).ker :=
  ((TensorProduct.map (IdealTensorCoefficientTransition.quotientTransition
    (algebraMap R S) I) (unit S P)).comp (f.lTensor (R ⧸ I)).ker.subtype).codRestrict _
      fun z ↦ by
        change (f.baseChange S).lTensor _ (TensorProduct.map _ _ z.val) = 0
        rw [IdealTensorCoefficientTransition.differential_naturality
          (algebraMap R S) f (f.baseChange S) _ (unit S P) (unit S N)
          (differential S f), z.property, map_zero]

/-- The relation transition has the expected underlying semilinear tensor map. -/
theorem relation_val (f : P →ₗ[R] N) (z : (f.lTensor (R ⧸ I)).ker) :
    (relation S I f z).val = TensorProduct.map
      (IdealTensorCoefficientTransition.quotientTransition (algebraMap R S) I)
      (unit S P) z.val := rfl

attribute [local instance] quotientAlgebra quotientTower

/-- The explicit relation transition equals the generator from residual kernel lifting. -/
theorem relation_eq_expand (f : P →ₗ[R] N) (z : (f.baseChange (R ⧸ I)).ker) :
    relation S I f ⟨z.val, z.property⟩ =
      ScalarPresentationKernel.expand S (S ⧸ I.map (algebraMap R S)) f
        (ResidualKernelSpan.comparison (R ⧸ I) (S ⧸ I.map (algebraMap R S)) f
          (1 ⊗ₜ[R ⧸ I] z)) := by
  apply Subtype.ext
  apply (AlgebraTensorModule.cancelBaseChange R S
    (S ⧸ I.map (algebraMap R S)) (S ⧸ I.map (algebraMap R S)) P).injective
  rw [ScalarPresentationKernel.expand_val, LinearEquiv.apply_symm_apply, relation_val]
  exact quotient_cancel S I z.val

/-- Killing these actual old relation images kills any linear map on the new kernel. -/
theorem map_eq_zero {T : Type*} [AddCommGroup T] [Module S T]
    (f : P →ₗ[R] N) (q : N →ₗ[R] M)
    (he : Function.Exact f q) (hq : Function.Surjective q)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)]
    (g : ((f.baseChange S).lTensor (S ⧸ I.map (algebraMap R S))).ker →ₗ[S] T)
    (hg : ∀ z, g (relation S I f z) = 0) : g = 0 := by
  apply ScalarPresentationKernel.map_eq_zero S (S ⧸ I.map (algebraMap R S)) (R ⧸ I)
    Ideal.Quotient.mk_surjective f q he hq g
  intro z
  rw [← relation_eq_expand]
  exact hg _

end FLT.Mazur.IdealResidualKernelSpan

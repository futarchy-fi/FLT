/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FlatTensorHomKernel

/-! # Relation functionals after extension from the original base to a test algebra -/

@[expose] public noncomputable section
open TensorProduct
namespace LinearMap
variable {R B U V M : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [AddCommGroup U] [AddCommGroup V] [AddCommGroup M]
  [Module R U] [Module R V] [Module R M] [Module B M] [IsScalarTower R B M]

/-- The tensor/Hom adjunction, with its coefficient-algebra linearity retained. -/
def scalarExtensionHomEquiv : (B ⊗[R] V →ₗ[B] M) ≃ₗ[B] (V →ₗ[R] M) :=
  (AlgebraTensorModule.lift.equiv R B B B V M).symm.trans
    (ringLmapEquivSelf B B (V →ₗ[R] M))

/-- Restriction evaluates at the original coordinate inside the scalar extension. -/
theorem scalarExtensionHomEquiv_apply (f : B ⊗[R] V →ₗ[B] M) (v : V) :
    scalarExtensionHomEquiv f v = f (1 ⊗ₜ[R] v) := rfl

/-- Extension evaluates using the actual test-algebra scalar action. -/
theorem scalarExtensionHomEquiv_symm_tmul (f : V →ₗ[R] M) (b : B) (v : V) :
    scalarExtensionHomEquiv.symm f (b ⊗ₜ[R] v) = b • f v := rfl

/-- Precomposition with original relations is linear over the coefficient algebra. -/
def relativeRelationPrecomp (r : U →ₗ[R] V) : (V →ₗ[R] M) →ₗ[B] (U →ₗ[R] M) where
  toFun f := f.comp r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Original relation functionals are precisely the functionals on the extended relations. -/
def relativeRelationKernelEquiv (r : U →ₗ[R] V) :
    ker (relationPrecomp (M := M) (r.baseChange B)) ≃ₗ[B]
      ker (relativeRelationPrecomp (B := B) (M := M) r) where
  toFun f := ⟨scalarExtensionHomEquiv f.val, by
    apply LinearMap.ext
    intro u
    change f.val (1 ⊗ₜ[R] r u) = 0
    exact LinearMap.congr_fun f.property (1 ⊗ₜ[R] u)⟩
  invFun f := ⟨scalarExtensionHomEquiv.symm f.val, by
    apply AlgebraTensorModule.ext
    intro b u
    change scalarExtensionHomEquiv.symm f.val (b ⊗ₜ[R] r u) = 0
    rw [scalarExtensionHomEquiv_symm_tmul]
    have hf : f.val (r u) = 0 := LinearMap.congr_fun f.property u
    rw [hf, smul_zero]⟩
  left_inv f := by apply Subtype.ext; exact LinearEquiv.symm_apply_apply _ _
  right_inv f := by apply Subtype.ext; exact LinearEquiv.apply_symm_apply _ _
  map_add' f g := by apply Subtype.ext; exact map_add _ _ _
  map_smul' b f := by apply Subtype.ext; exact map_smul _ _ _

end LinearMap

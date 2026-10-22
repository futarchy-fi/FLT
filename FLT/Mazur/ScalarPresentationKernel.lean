/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ResidualKernelSpan

/-!
# Cancelling scalars in a presentation kernel

The canonical tensor cancellation equivalence identifies relations in an
iterated scalar extension with relations after the composite extension.
This comparison retains linearity over the intermediate scalar ring.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ScalarPresentationKernel
variable {R P N : Type*} [CommRing R]
  [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
  (S B : Type*) [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]

/-- Cancellation intertwines the two presentation differentials. -/
theorem differential_cancel (f : P →ₗ[R] N) (z : B ⊗[S] (S ⊗[R] P)) :
    f.baseChange B (AlgebraTensorModule.cancelBaseChange R S B B P z) =
      AlgebraTensorModule.cancelBaseChange R S B B N
        ((f.baseChange S).baseChange B z) := by
  rw [LinearMap.baseChange_baseChange]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/-- Expand a relation along the canonical scalar-cancellation equivalence. -/
def expand (f : P →ₗ[R] N) :
    (f.baseChange B).ker ≃ₗ[B] ((f.baseChange S).baseChange B).ker where
  toFun z := ⟨(AlgebraTensorModule.cancelBaseChange R S B B P).symm z.val, by
    apply (AlgebraTensorModule.cancelBaseChange R S B B N).injective
    rw [← differential_cancel, LinearEquiv.apply_symm_apply, z.property, map_zero]⟩
  invFun z := ⟨AlgebraTensorModule.cancelBaseChange R S B B P z.val, by
    change f.baseChange B (AlgebraTensorModule.cancelBaseChange R S B B P z.val) = 0
    rw [differential_cancel, z.property, map_zero]⟩
  left_inv z := Subtype.ext (LinearEquiv.apply_symm_apply _ _)
  right_inv z := Subtype.ext (LinearEquiv.symm_apply_apply _ _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' b x := Subtype.ext (map_smul _ _ _)

/-- Expansion on underlying tensors is inverse scalar cancellation. -/
theorem expand_val (f : P →ₗ[R] N) (z : (f.baseChange B).ker) :
    (expand S B f z).val =
      (AlgebraTensorModule.cancelBaseChange R S B B P).symm z.val := rfl

variable {M : Type*} [AddCommGroup M] [Module R M]
  (A : Type*) [CommRing A] [Algebra R A] [Algebra A B] [IsScalarTower R A B]
  {T : Type*} [AddCommGroup T] [Module S T]

/-- Every linear map out of the actual iterated kernel is determined by old relations. -/
theorem map_eq_zero (hB : Function.Surjective (algebraMap S B))
    (f : P →ₗ[R] N) (q : N →ₗ[R] M)
    (he : Function.Exact f q) (hq : Function.Surjective q)
    [Module.Flat A (A ⊗[R] M)]
    (g : ((f.baseChange S).baseChange B).ker →ₗ[S] T)
    (hg : ∀ x : (f.baseChange A).ker,
      g (expand S B f (ResidualKernelSpan.comparison A B f (1 ⊗ₜ[A] x))) = 0) :
    g = 0 := by
  have h := ResidualKernelSpan.map_eq_zero A B S hB f q he hq
    (g.comp ((expand S B f).toLinearMap.restrictScalars S)) hg
  ext z
  obtain ⟨y, rfl⟩ := (expand S B f).surjective z
  exact LinearMap.congr_fun h y

end FLT.Mazur.ScalarPresentationKernel

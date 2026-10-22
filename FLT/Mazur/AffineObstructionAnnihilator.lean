/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineObstructionBaseChange
public import FLT.Mazur.IdealObstructionAnnihilator

/-!
# Annihilators of the actual affine obstruction

The connecting argument is transported to the module-first tensor orientation.
A linear map killing the original affine obstruction images kills every element
of the new obstruction. This permits testing vanishing only after localization.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.AffineObstructionAnnihilator
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (S : Type*) [CommRing S] [Algebra R S] (I : Ideal R)
  [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] A)]
  {T : Type*} [AddCommGroup T] [Module S T]
  (g : (S ⊗[R] A) ⊗[S] I.map (algebraMap R S) →ₗ[S] T)

/-- Old affine obstruction images determine every linear annihilator of the new obstruction. -/
theorem map_kernel_eq_zero
    (h : ∀ z : IdealTensorKernel.obstruction (S := A) I,
      g (IdealTensorKernel.transition (algebraMap R S)
        (AffineObstructionBaseChange.rightMap S) (AffineObstructionBaseChange.square S)
        I z.val) = 0)
    (z : IdealTensorKernel.obstruction (S := S ⊗[R] A) (I.map (algebraMap R S))) :
    g z.val = 0 := by
  let J := I.map (algebraMap R S)
  let e := TensorProduct.comm S J (S ⊗[R] A)
  have hz : e.symm z.val ∈ (J.subtype.rTensor (S ⊗[R] A)).ker := by
    apply (TensorProduct.lid S (S ⊗[R] A)).injective
    rw [map_zero, ← IdealObstructionOrientation.inclusion_flip (S := S),
      LinearEquiv.apply_symm_apply]
    exact z.property
  have hh := IdealObstructionAnnihilator.map_kernel_eq_zero_of_residual_flat
    S I (g.comp e.toLinearMap) ?_ ⟨e.symm z.val, hz⟩
  · simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using hh
  intro w
  have hw : TensorProduct.comm R I A w.val ∈ IdealTensorKernel.obstruction (S := A) I := by
    change ModuleIdealTensor.inclusion (S := A) I (TensorProduct.comm R I A w.val) = 0
    rw [IdealObstructionOrientation.inclusion_flip, w.property, map_zero]
  change g (TensorProduct.comm S J (S ⊗[R] A) _) = 0
  rw [IdealObstructionOrientation.transition_flip, ← AffineObstructionBaseChange.transition_eq]
  exact h ⟨_, hw⟩

end FLT.Mazur.AffineObstructionAnnihilator

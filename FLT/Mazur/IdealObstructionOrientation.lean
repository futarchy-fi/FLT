/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealObstructionUnitCriterion

/-!
# Comparing the two tensor orientations for ideal obstructions

Tensor commutativity carries the connecting-map obstruction to the
module-first multiplication kernel used by the affine flatness criterion.
The comparison also commutes with the actual semilinear transition.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.IdealObstructionOrientation
variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- Flipping the ideal tensor carries its inclusion to the actual module multiplication. -/
theorem inclusion_flip (I : Ideal R) (z : I ⊗[R] M) :
    ModuleIdealTensor.inclusion (S := S) I (TensorProduct.comm R I M z) =
      TensorProduct.lid R M (I.subtype.rTensor M z) := by
  induction z with
  | tmul a m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable {R' M' : Type*} [CommRing R'] [AddCommGroup M'] [Module R' M']

omit [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M] in
/-- Tensor flipping commutes with simultaneous changes of ideal coefficients and module. -/
theorem transition_flip (r : R →+* R') (I : Ideal R) (c : M →ₛₗ[r] M') (z : I ⊗[R] M) :
    TensorProduct.comm R' (I.map r) M'
      (TensorProduct.map (IdealTensorKernel.idealTransition r I) c z) =
    TensorProduct.map c (IdealTensorKernel.idealTransition r I) (TensorProduct.comm R I M z) := by
  induction z with
  | tmul a m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable (R') [Algebra R R'] (I : Ideal R)
  [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)]

include S in
/-- The module-first obstruction transition gives injectivity in the connecting orientation. -/
theorem ideal_injective
    (h : ∀ z : (ModuleIdealTensor.inclusion (S := S) (M := M) I).ker,
      TensorProduct.map (ScalarExtensionUnit.unit R' M)
        (IdealTensorKernel.idealTransition (algebraMap R R') I) z.val = 0) :
    Function.Injective ((I.map (algebraMap R R')).subtype.rTensor (R' ⊗[R] M)) := by
  apply IdealObstructionUnitCriterion.ideal_injective R' I
  intro z
  have hz : ModuleIdealTensor.inclusion (S := S) I (TensorProduct.comm R I M z.val) = 0 := by
    rw [inclusion_flip, z.property, map_zero]
  apply (TensorProduct.comm R' (I.map (algebraMap R R')) (R' ⊗[R] M)).injective
  rw [map_zero, transition_flip]
  exact h ⟨_, hz⟩

include S in
/-- The same vanishing proves injectivity of the actual new module multiplication map. -/
theorem inclusion_injective
    (h : ∀ z : (ModuleIdealTensor.inclusion (S := S) (M := M) I).ker,
      TensorProduct.map (ScalarExtensionUnit.unit R' M)
        (IdealTensorKernel.idealTransition (algebraMap R R') I) z.val = 0) :
    Function.Injective (ModuleIdealTensor.inclusion (S := R') (M := R' ⊗[R] M)
      (I.map (algebraMap R R'))) :=
  (AlgebraTensorModule.rid R' R' (R' ⊗[R] M)).injective.comp
    (((I.map (algebraMap R R')).subtype.lTensor_inj_iff_rTensor_inj (R' ⊗[R] M)).mpr
      (ideal_injective (S := S) R' I h))

end FLT.Mazur.IdealObstructionOrientation

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.ULiftHardlyRamified

/-! # Recovering the original generic member after independent universe lifts -/

@[expose] public noncomputable section
attribute [local instance 2000] TensorProduct.leftModule
attribute [local instance] ULift.algebra'
open scoped TensorProduct
open TensorProduct
universe u v
namespace GaloisRepresentation
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  (E : Type*) [CommRing E] [Algebra R E]

/-- The actual lifted tensor product cancels back to the original generic module. -/
def uliftGenericEquiv :
    E ⊗[ULift.{u} R] ULift.{v} V ≃ₗ[E] E ⊗[R] V :=
  ((uliftCoefficientTensor (R := R) (V := V)).symm.baseChange (ULift.{u} R) E _ _).trans
    (AlgebraTensorModule.cancelBaseChange R (ULift.{u} R) E E V)

/-- Cancellation retains the original pure tensor, including its coefficient. -/
@[simp] theorem uliftGenericEquiv_tmul (a : E) (x : V) :
    uliftGenericEquiv E (a ⊗ₜ[ULift.{u} R] (ULift.up x : ULift.{v} V)) = a ⊗ₜ[R] x := by
  simp [uliftGenericEquiv, uliftCoefficientTensor_symm_up]

variable [TopologicalSpace R] [TopologicalSpace E] [IsTopologicalRing E] [ContinuousSMul R E]

/-- Lifted scalars act continuously through their original values. -/
instance uliftScalarsContinuousSMul : ContinuousSMul (ULift.{u} R) E where
  continuous_smul := by
    change Continuous (fun x : ULift.{u} R × E ↦ x.1.down • x.2)
    exact (continuous_uliftDown.comp continuous_fst).smul continuous_snd

variable [IsLocalRing R] [IsTopologicalRing R] [Module.Finite R V] [Module.Free R V]

omit [IsLocalRing R] in
/-- The lifted representation acts on the same original vector under the lift. -/
@[simp] theorem uliftCoefficients_apply (ρ : GaloisRep ℚ R V)
    (g : Field.absoluteGaloisGroup ℚ) (x : V) :
    uliftCoefficients.{u, v} ρ g (ULift.up x) = ULift.up (ρ g x) := by
  change uliftCoefficientTensor.{u, v}
    ((ρ g).baseChange (ULift.{u} R) (uliftCoefficientTensor.{u, v}.symm (ULift.up x))) = _
  rw [uliftCoefficientTensor_symm_up, LinearMap.baseChange_tmul,
    uliftCoefficientTensor_tmul]
  simp

omit [IsLocalRing R] in
/-- After scalar extension, the actual lifted representation recovers the original one. -/
theorem uliftCoefficients_generic (ρ : GaloisRep ℚ R V) :
    ((uliftCoefficients.{u, v} ρ).baseChange E).conj (uliftGenericEquiv E) =
      ρ.baseChange E := by
  let e := uliftGenericEquiv (R := R) (V := V) E
  have he (g : Field.absoluteGaloisGroup ℚ) (x : E ⊗[ULift.{u} R] ULift.{v} V) :
      e (((uliftCoefficients ρ).baseChange E) g x) = (ρ.baseChange E) g (e x) := by
    induction x using TensorProduct.inductionOn with
    | tmul a x =>
      obtain ⟨x⟩ := x
      simp only [GaloisRep.baseChange_tmul, uliftCoefficients_apply, e, uliftGenericEquiv_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  let := moduleTopology E (Module.End E (E ⊗[R] V))
  apply ContinuousMonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  change e (((uliftCoefficients ρ).baseChange E) g (e.symm x)) = (ρ.baseChange E) g x
  rw [he, e.apply_symm_apply]

end GaloisRepresentation

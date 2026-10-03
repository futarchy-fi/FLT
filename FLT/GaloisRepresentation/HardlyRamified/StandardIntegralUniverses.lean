/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.StandardFamilyMember
public import FLT.GaloisRepresentation.HardlyRamified.ULiftGenericRecovery

/-! # Standard integral family witnesses in the target's independent universes -/

@[expose] public noncomputable section
attribute [local instance 2000] TensorProduct.leftModule
attribute [local instance] ULift.algebra'
open scoped TensorProduct
universe u v
namespace GaloisRepresentation
variable (p : ℕ) [Fact p.Prime]

/-- The standard member has an actual hardly ramified integral model in any two universes. -/
theorem standardFamilyMember_integral_universes (hp : Odd p) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLocalRing A) (_ : Algebra ℤ_[p] A) (_ : Module.Finite ℤ_[p] A)
      (_ : Module.Free ℤ_[p] A) (_ : IsDomain A) (_ : Algebra A (AlgebraicClosure ℚ_[p]))
      (_ : IsScalarTower ℤ_[p] A (AlgebraicClosure ℚ_[p])) (_ : IsModuleTopology ℤ_[p] A)
      (_ : ContinuousSMul A (AlgebraicClosure ℚ_[p]))
      (W : Type v) (_ : AddCommGroup W) (_ : Module A W) (_ : Module.Finite A W)
      (_ : Module.Free A W) (hW : Module.rank A W = 2) (τ : GaloisRep ℚ A W)
      (r : AlgebraicClosure ℚ_[p] ⊗[A] W ≃ₗ[AlgebraicClosure ℚ_[p]]
        (Fin 2 → AlgebraicClosure ℚ_[p])),
      IsHardlyRamified hp hW τ ∧
        (τ.baseChange (AlgebraicClosure ℚ_[p])).conj r = standardFamilyMember p := by
  let A := ULift.{u} ℤ_[p]
  let W := ULift.{v} (ℤ_[p] × ℤ_[p])
  let : IsDomain A := (ULift.ringEquiv : A ≃+* ℤ_[p]).isDomain
  let : IsModuleTopology ℤ_[p] A :=
    IsModuleTopology.iso (ContinuousLinearEquiv.ulift (R₁ := ℤ_[p]) (M₁ := ℤ_[p])).symm
  let τ : GaloisRep ℚ A W := uliftCoefficients (cyclotomicTrivial p)
  let j := uliftGenericEquiv (R := ℤ_[p]) (V := ℤ_[p] × ℤ_[p]) (AlgebraicClosure ℚ_[p])
  let f := rankTwoFrame (AlgebraicClosure ℚ_[p]) (cyclotomicTrivial_rank p)
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, W, inferInstance, inferInstance, inferInstance, inferInstance,
    uliftCoefficients_rank (cyclotomicTrivial_rank p), τ, j.trans f, ?_, ?_⟩
  · exact (cyclotomicTrivial_hardlyRamified p hp).uliftCoefficients hp (cyclotomicTrivial_rank p)
  · change ((((uliftCoefficients (cyclotomicTrivial p)).baseChange
      (AlgebraicClosure ℚ_[p])).conj j).conj f) = standardFamilyMember p
    rw [uliftCoefficients_generic]
    rfl

end GaloisRepresentation

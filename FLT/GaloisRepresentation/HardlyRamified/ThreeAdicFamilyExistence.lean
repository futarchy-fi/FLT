/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.ThreeAdicFamilyCompatibility
public import FLT.GaloisRepresentation.HardlyRamified.ThreeAdicFamilyIntegralModels

/-! # The original three-adic representation belongs to a compatible family

This is the three-adic specialization of the original family target, with
independent original universes and the actual original member retained.
The general-prime family theorem remains a separate obligation.
-/

@[expose] public noncomputable section
open scoped TensorProduct
universe u v
namespace GaloisRepresentation.IsHardlyRamified
variable {R : Type u} {V : Type v} [CommRing R] [IsDomain R] [IsLocalRing R]
  [Algebra ℤ_[3] R] [Module.Free ℤ_[3] R] [Module.Finite ℤ_[3] R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[3] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}

/-- The exact family target is proved for the original three-adic member in its own universes. -/
theorem mem_isCompatible_three_universes
    (hρ : IsHardlyRamified (⟨1, rfl⟩ : Odd 3) hV ρ) :
    ∃ (E : Type v) (_ : Field E) (_ : NumberField E) (σ : GaloisRepFamily ℚ E 2),
      σ.isCompatible ∧
      (∀ {p : ℕ} (hp : Fact p.Prime) (hodd : Odd p) (φ : E →+* AlgebraicClosure ℚ_[p]),
        ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
          (_ : IsLocalRing A) (_ : Algebra ℤ_[p] A) (_ : Module.Finite ℤ_[p] A)
          (_ : Module.Free ℤ_[p] A) (_ : IsDomain A) (_ : Algebra A (AlgebraicClosure ℚ_[p]))
          (_ : IsScalarTower ℤ_[p] A (AlgebraicClosure ℚ_[p])) (_ : IsModuleTopology ℤ_[p] A)
          (_ : ContinuousSMul A (AlgebraicClosure ℚ_[p]))
          (W : Type v) (_ : AddCommGroup W) (_ : Module A W) (_ : Module.Finite A W)
          (_ : Module.Free A W) (hW : Module.rank A W = 2) (τ : GaloisRep ℚ A W)
          (r : AlgebraicClosure ℚ_[p] ⊗[A] W ≃ₗ[AlgebraicClosure ℚ_[p]]
            (Fin 2 → AlgebraicClosure ℚ_[p])),
          IsHardlyRamified hodd hW τ ∧ (τ.baseChange (AlgebraicClosure ℚ_[p])).conj r = σ hp φ) ∧
      (∃ (_ : Algebra R (AlgebraicClosure ℚ_[3]))
        (_ : ContinuousSMul R (AlgebraicClosure ℚ_[3])) (ψ : E →+* AlgebraicClosure ℚ_[3])
        (r : AlgebraicClosure ℚ_[3] ⊗[R] V ≃ₗ[AlgebraicClosure ℚ_[3]]
          (Fin 2 → AlgebraicClosure ℚ_[3])),
        (ρ.baseChange (AlgebraicClosure ℚ_[3])).conj r = σ inferInstance ψ) := by
  let := PadicOrderEmbedding.algebra 3 R
  let := PadicOrderEmbedding.scalarTower 3 R
  let := PadicOrderEmbedding.continuousSMul 3 R
  let E := ULift.{v} ℚ
  let : NumberField E := NumberField.of_ringEquiv ℚ E (ULift.ringEquiv : E ≃+* ℚ).symm
  let ψ : E →+* AlgebraicClosure ℚ_[3] :=
    (algebraMap ℚ _).comp ULift.ringEquiv.toRingHom
  refine ⟨E, inferInstance, inferInstance, originalThreeAdicFamily E hV ρ,
    originalThreeAdicFamily_compatible E hV hρ,
    fun hp hodd φ ↦ originalThreeAdicFamily_integral E hV hρ hp hodd φ,
    inferInstance, inferInstance, ψ, rankTwoFrame (AlgebraicClosure ℚ_[3]) hV, ?_⟩
  exact (originalThreeAdicFamily_three E hV ρ ψ).symm

end GaloisRepresentation.IsHardlyRamified

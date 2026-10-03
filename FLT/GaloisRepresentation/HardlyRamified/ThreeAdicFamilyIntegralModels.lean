/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.ThreeAdicFamily
public import FLT.GaloisRepresentation.HardlyRamified.StandardIntegralUniverses

/-! # Integral models for every odd-prime member of the dependent family -/

@[expose] public noncomputable section
open scoped TensorProduct
universe u v
namespace GaloisRepresentation
variable (E : Type*) [Field E] [NumberField E]
  {R : Type u} {V : Type v} [CommRing R] [IsDomain R] [IsLocalRing R]
  [Algebra ℤ_[3] R] [Module.Free ℤ_[3] R] [Module.Finite ℤ_[3] R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[3] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  [Algebra R (AlgebraicClosure ℚ_[3])] [IsScalarTower ℤ_[3] R (AlgebraicClosure ℚ_[3])]
  [ContinuousSMul R (AlgebraicClosure ℚ_[3])]
  (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}

/-- At three use the original integral representation; elsewhere use the lifted standard model. -/
theorem originalThreeAdicFamily_integral
    (hρ : IsHardlyRamified (⟨1, rfl⟩ : Odd 3) hV ρ)
    {p : ℕ} (hp : Fact p.Prime) (hodd : Odd p) (φ : E →+* AlgebraicClosure ℚ_[p]) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLocalRing A) (_ : Algebra ℤ_[p] A) (_ : Module.Finite ℤ_[p] A)
      (_ : Module.Free ℤ_[p] A) (_ : IsDomain A) (_ : Algebra A (AlgebraicClosure ℚ_[p]))
      (_ : IsScalarTower ℤ_[p] A (AlgebraicClosure ℚ_[p])) (_ : IsModuleTopology ℤ_[p] A)
      (_ : ContinuousSMul A (AlgebraicClosure ℚ_[p]))
      (W : Type v) (_ : AddCommGroup W) (_ : Module A W) (_ : Module.Finite A W)
      (_ : Module.Free A W) (hW : Module.rank A W = 2) (τ : GaloisRep ℚ A W)
      (r : AlgebraicClosure ℚ_[p] ⊗[A] W ≃ₗ[AlgebraicClosure ℚ_[p]]
        (Fin 2 → AlgebraicClosure ℚ_[p])),
      IsHardlyRamified hodd hW τ ∧
        (τ.baseChange (AlgebraicClosure ℚ_[p])).conj r = originalThreeAdicFamily E hV ρ hp φ := by
  by_cases hp3 : p = 3
  · subst p
    refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, V, inferInstance, inferInstance, inferInstance, inferInstance,
      hV, ρ, rankTwoFrame (AlgebraicClosure ℚ_[3]) hV, hρ, ?_⟩
    exact (originalThreeAdicFamily_three E hV ρ φ).symm
  · simpa only [originalThreeAdicFamily, threeAdicFamily_ne_three E _ hp φ hp3] using
      standardFamilyMember_integral_universes.{u, v} p hodd

end GaloisRepresentation

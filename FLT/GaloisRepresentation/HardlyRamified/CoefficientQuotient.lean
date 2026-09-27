/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.B5Inputs

/-!
# Hardly ramified representations over quotient coefficient rings

Hardly ramified representations remain hardly ramified after a surjective
change of coefficients, including to residue coefficient rings.
-/

@[expose] public section

open scoped TensorProduct
open TensorProduct

namespace GaloisRepresentation.B5Inputs

set_option backward.isDefEq.respectTransparency false in
/-- A surjective change of coefficients preserves hardly ramified representations.
The coefficient rings need not be finite free over the p-adic integers. -/
@[nolint unusedArguments]
theorem hardlyRamified_of_surjective_coefficients {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    {R A : Type} [CommRing R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Algebra ℤ_[p] R]
    [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Algebra ℤ_[p] A] [Algebra R A] [IsScalarTower ℤ_[p] R A]
    [ContinuousSMul R A] (hsurj : Function.Surjective (algebraMap R A))
    {V : Type} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) (hVA : Module.rank A (A ⊗[R] V) = 2)
    {ρ : GaloisRep ℚ R V} (hρ : IsHardlyRamified hpodd hV ρ) :
    IsHardlyRamified hpodd hVA (ρ.baseChange A) := by
  refine ⟨?_, ?_, flatAt_quotient hsurj ρ _ hρ.isFlat, ?_⟩
  · intro g
    change ((ρ g).baseChange A).det = _
    rw [LinearMap.det_baseChange]
    change algebraMap R A (ρ.det g) = _
    rw [hρ.det, ← IsScalarTower.algebraMap_apply ℤ_[p] R A]
  · intro q hq hgood
    have := hρ.isUnramified q hq hgood
    infer_instance
  · obtain ⟨π, hπ, δ, hδ⟩ := hρ.isTameAtTwo
    let e : A ⊗[R] R ≃ₗ[A] A := AlgebraTensorModule.rid R A A
    let πA : A ⊗[R] V →ₗ[A] A := e.toLinearMap.comp (π.baseChange A)
    let δA := (δ.baseChange A).conj e
    have hker : δ.ker ≤ δA.ker := by
      dsimp [δA]
      rw [GaloisRep.ker_conj]
      exact δ.ker_baseChange
    refine ⟨πA, e.surjective.comp (π.baseChange_surjective A hπ), δA, ?_⟩
    intro g x
    refine ⟨?_, (hδ 1 0).2.1.trans hker, ?_⟩
    · induction x using TensorProduct.inductionOn with
      | tmul a v =>
        have hv := (hδ g v).1
        have hδlin : δ g (π v) = π v • δ g 1 := by
          simpa using (δ g).map_smul (π v) (1 : R)
        simp only [GaloisRep.baseChange_map, GaloisRep.baseChange_tmul,
          πA, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul,
          e, AlgebraTensorModule.rid_tmul, δA, GaloisRep.conj_apply_apply,
          AlgebraTensorModule.rid_symm_apply]
        rw [hv, hδlin]
        simp [smul_smul, mul_comm]
      | add x y hx hy => simp_all
    · intro g
      have hgg : g * g ∈ δ.ker := by
        change δ (g * g) = 1
        rw [map_mul, (hδ 1 0).2.2 g]
      have hggA := hker hgg
      change δA (g * g) = 1 at hggA
      rwa [map_mul] at hggA

end GaloisRepresentation.B5Inputs

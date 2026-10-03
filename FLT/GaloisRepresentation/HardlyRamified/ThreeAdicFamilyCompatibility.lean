/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.ThreeAdicFamily
public import FLT.GaloisRepresentation.HardlyRamified.ThreeAdicPolynomialUniverses

/-! # Compatibility of the dependent family containing the original member -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
open NumberField IsDedekindDomain Polynomial
namespace GaloisRepresentation
variable (E : Type*) [Field E] [NumberField E]
  {R V : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  [Algebra ℤ_[3] R] [Module.Free ℤ_[3] R] [Module.Finite ℤ_[3] R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[3] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  [Algebra R (AlgebraicClosure ℚ_[3])] [ContinuousSMul R (AlgebraicClosure ℚ_[3])]
  (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}

/-- The family is weakly compatible with exceptional set consisting only of the place at two. -/
theorem originalThreeAdicFamily_compatible
    (hρ : IsHardlyRamified (⟨1, rfl⟩ : Odd 3) hV ρ) :
    GaloisRepFamily.isCompatible (originalThreeAdicFamily E hV ρ) := by
  classical
  let v₂ := Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (by decide : Nat.Prime 2)
  refine ⟨{v₂}, fun v ↦ (X - 1) *
    (X - C ((Rat.HeightOneSpectrum.primesEquiv v).val : E)), ?_⟩
  intro p hp φ v hv hvp
  let q := Rat.HeightOneSpectrum.primesEquiv v
  have he : q.property.toHeightOneSpectrumRingOfIntegersRat = v := by
    apply Rat.HeightOneSpectrum.primesEquiv.injective
    exact ThreeAdicPlan.primesEquiv_ratPrime q.val q.property
  have hq2 : q.val ≠ 2 := by
    intro h
    have hplace : q.property.toHeightOneSpectrumRingOfIntegersRat = v₂ := by
      apply Rat.HeightOneSpectrum.primesEquiv.injective
      rw [ThreeAdicPlan.primesEquiv_ratPrime, ThreeAdicPlan.primesEquiv_ratPrime]
      exact Subtype.ext h
    exact hv (Finset.mem_singleton.mpr (he.symm.trans hplace))
  have hqp : q.val ≠ p := by
    intro h
    apply hvp
    rw [← he, ← h]
    change Rat.ringOfIntegersEquiv (q.val : 𝓞 ℚ) ∈ Ideal.span {(q.val : ℤ)}
    simp
  rw [← he]
  dsimp only [originalThreeAdicFamily]
  by_cases hp3 : p = 3
  · subst p
    rw [threeAdicFamily_three]
    unfold originalThreeAdicMember
    constructor
    · let := hρ.isUnramified q.val q.property ⟨hq2, hqp⟩
      infer_instance
    · have h := IsHardlyRamified.framed_frobenius_three_universes hV hρ
        (AlgebraicClosure ℚ_[3]) (algebraMap ℚ _)
        (rankTwoFrame (AlgebraicClosure ℚ_[3]) hV) q.val q.property hqp
      simpa [cyclotomicTrivialPolynomial, ThreeAdicPlan.primesEquiv_ratPrime, q] using h
  · rw [threeAdicFamily_ne_three E _ hp φ hp3]
    constructor
    · exact standardFamilyMember_unramified p q.val q.property hqp
    · simpa [ThreeAdicPlan.primesEquiv_ratPrime, q] using
        standardFamilyMember_frobenius p q.val q.property hqp

end GaloisRepresentation

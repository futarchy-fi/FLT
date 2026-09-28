/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalPolynomialObstruction
public import FLT.Mathlib.RingTheory.DiscreteValuationRing.EisensteinExtension
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Realizing finite coefficient DVR extensions as three-adic integer rings

A finite DVR over a finite three-adic coefficient ring is the full ring of
integers of its fraction field. The realization preserves coefficient maps,
additive valuations, and the product formula for degrees.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- A finite coefficient-DVR extension realizes a finite three-adic field
with its full integer ring and the expected absolute degree. -/
theorem existsThreeAdicDvrRealization
    (C S E : Type) [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Algebra ℤ_[3] C] [Module.Finite ℤ_[3] C] [FaithfulSMul ℤ_[3] C]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra C S] [Module.Finite C S] [FaithfulSMul C S]
    [Field E] [Algebra C E] [Algebra S E] [IsScalarTower C S E] [IsFractionRing S E] :
    ∃ (_ : Algebra ℚ_[3] E) (_ : Algebra ℤ_[3] E)
      (_ : IsScalarTower ℤ_[3] ℚ_[3] E) (_ : FiniteDimensional ℚ_[3] E)
      (_ : Algebra C (ThreeAdicIntegers E))
      (_ : IsScalarTower ℤ_[3] C (ThreeAdicIntegers E))
      (j : S ≃ₐ[C] ThreeAdicIntegers E),
      Module.finrank ℚ_[3] E = Module.finrank ℤ_[3] C * Module.finrank C S ∧
        ∀ x : S, IsDiscreteValuationRing.addVal (ThreeAdicIntegers E) (j x) =
          IsDiscreteValuationRing.addVal S x := by
  let instAlgS : Algebra ℤ_[3] S := Algebra.compHom S (algebraMap ℤ_[3] C)
  let instAlgE : Algebra ℤ_[3] E := Algebra.compHom E (algebraMap ℤ_[3] C)
  let instTowerS : IsScalarTower ℤ_[3] C S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let instTowerE : IsScalarTower ℤ_[3] C E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let instTowerSE : IsScalarTower ℤ_[3] S E := IsScalarTower.to₁₃₄ ℤ_[3] C S E
  have hinj : Function.Injective (algebraMap ℤ_[3] E) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[3] S E,
      IsScalarTower.algebraMap_eq ℤ_[3] C S]
    exact (IsFractionRing.injective S E).comp
      ((FaithfulSMul.algebraMap_injective C S).comp (FaithfulSMul.algebraMap_injective ℤ_[3] C))
  let instAlgQ : Algebra ℚ_[3] E := (IsFractionRing.lift (K := ℚ_[3]) hinj).toAlgebra
  let instTowerQ : IsScalarTower ℤ_[3] ℚ_[3] E :=
    IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hinj x).symm
  let instFiniteS : Module.Finite ℤ_[3] S := Module.Finite.trans C S
  let instFaithfulS : FaithfulSMul ℤ_[3] S :=
    (faithfulSMul_iff_algebraMap_injective ℤ_[3] S).mpr
      ((FaithfulSMul.algebraMap_injective C S).comp (FaithfulSMul.algebraMap_injective ℤ_[3] C))
  let instFiniteE : FiniteDimensional ℚ_[3] E := Module.finite_of_finrank_pos (by
    rw [IsFractionRing.finrank_eq ℤ_[3] ℚ_[3] S E]
    exact Module.finrank_pos)
  let instClosure : IsIntegralClosure S ℤ_[3] E :=
    IsIntegralClosure.of_isIntegrallyClosed S ℤ_[3] E
  let j := IsIntegralClosure.equiv ℤ_[3] S E (ThreeAdicIntegers E)
  let instAlgInt : Algebra C (ThreeAdicIntegers E) :=
    (j.toRingHom.comp (algebraMap C S)).toAlgebra
  let instTowerInt : IsScalarTower ℤ_[3] C (ThreeAdicIntegers E) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap ℤ_[3] (ThreeAdicIntegers E) x = j (algebraMap C S (algebraMap ℤ_[3] C x))
      rw [← IsScalarTower.algebraMap_apply, j.commutes]
  let jC : S ≃ₐ[C] ThreeAdicIntegers E := { j.toRingEquiv with commutes' := fun _ => rfl }
  refine ⟨instAlgQ, instAlgE, instTowerQ, instFiniteE, instAlgInt, instTowerInt, jC, ?_,
    fun x => IsDiscreteValuationRing.addValRingEquiv jC.toRingEquiv x⟩
  rw [IsFractionRing.finrank_eq ℤ_[3] ℚ_[3] S E, Module.finrank_mul_finrank]

end ThreeAdicPlan

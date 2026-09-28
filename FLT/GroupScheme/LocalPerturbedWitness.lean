/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalDvrRealization

/-!
# Perturbed Eisenstein witnesses in finite three-adic fields

Every exponent above the Eisenstein degree is realized exactly by a polynomial
value in a finite extension with the same degree and ramification index.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

namespace ThreeAdicPlan

/-- An exponent strictly above the degree produces a three-adic perturbation
witness with exact relative polynomial value and absolute degree. -/
theorem existsThreeAdicPerturbedWitness
    {C : Type} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Algebra ℤ_[3] C] [Module.Finite ℤ_[3] C] [FaithfulSMul ℤ_[3] C]
    (h3 : Irreducible (3 : C)) {P : C[X]} (hP : P.IsEisensteinAt (maximalIdeal C))
    (hPm : P.Monic) (hn : 0 < P.natDegree) (N : ℕ) (hN : P.natDegree < N) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra ℚ_[3] E) (_ : Algebra ℤ_[3] E)
      (_ : IsScalarTower ℤ_[3] ℚ_[3] E) (_ : FiniteDimensional ℚ_[3] E)
      (_ : Algebra C (ThreeAdicIntegers E))
      (_ : IsScalarTower ℤ_[3] C (ThreeAdicIntegers E))
      (_ : FaithfulSMul C (ThreeAdicIntegers E)) (y : ThreeAdicIntegers E),
      Module.finrank ℚ_[3] E = Module.finrank ℤ_[3] C * P.natDegree ∧
        threeAdicIdealOrder E (Ideal.span {(3 : ThreeAdicIntegers E)}) = P.natDegree ∧
        IsDiscreteValuationRing.addVal (ThreeAdicIntegers E) (aeval y P) = (N : ℕ∞) := by
  have hr : 0 < N / P.natDegree := Nat.div_pos hN.le hn
  have hs : N % P.natDegree < P.natDegree := Nat.mod_lt N hn
  have hr0 : N % P.natDegree = 0 → 2 ≤ N / P.natDegree := by
    intro hz
    by_contra h
    have hq : N / P.natDegree = 1 := by omega
    have he := Nat.mod_add_div N P.natDegree
    rw [hz, hq, mul_one, zero_add] at he
    omega
  obtain ⟨E, instField, instAlgK, instFiniteK, instAlgC, instTowerK, S, instRing,
    instDomain, instDvr, instAlgS, instFiniteS, instAlgSE, instTowerS, instFraction,
    instClosure, y, hdeg, hy, hval3, hvalP⟩ :=
      hP.existsPerturbedExtensionWithValuation (K := FractionRing C) hPm h3
        (N / P.natDegree) (N % P.natDegree) hr hs hr0
  have hinj : Function.Injective (algebraMap C E) := by
    rw [IsScalarTower.algebraMap_eq C (FractionRing C) E]
    exact (algebraMap (FractionRing C) E).injective.comp (IsFractionRing.injective C _)
  let instFaithfulS : FaithfulSMul C S :=
    (faithfulSMul_iff_algebraMap_injective C S).mpr fun x y h => hinj (by
      rw [IsScalarTower.algebraMap_apply C S E, IsScalarTower.algebraMap_apply C S E, h])
  obtain ⟨instAlgQ, instAlgZ, instTowerQ, instFiniteQ, instAlgInt, instTowerInt, j,
    hdegree, hv⟩ := existsThreeAdicDvrRealization C S E
  let instFaithfulInt : FaithfulSMul C (ThreeAdicIntegers E) :=
    (faithfulSMul_iff_algebraMap_injective C _).mpr fun x y h =>
      (FaithfulSMul.algebraMap_injective C S) (j.injective (by simpa using h))
  refine ⟨E, instField, instAlgQ, instAlgZ, instTowerQ, instFiniteQ, instAlgInt,
    instTowerInt, instFaithfulInt, j y, ?_, ?_, ?_⟩
  · rw [hdegree, ← IsFractionRing.finrank_eq C (FractionRing C) S E, hdeg]
  · have heq := (hv (3 : S)).trans (by simpa only [map_ofNat] using hval3)
    simp only [map_ofNat] at heq
    rw [threeAdicAddValEqIdealOrder E (3 : ThreeAdicIntegers E) (by
      let instCharZero : CharZero (ThreeAdicIntegers E) := Algebra.charZero_of_charZero ℤ_[3] _
      norm_num), ENat.natCast_inj] at heq
    exact heq
  · rw [aeval_algHom_apply, hv, hvalP, Nat.div_add_mod]

end ThreeAdicPlan

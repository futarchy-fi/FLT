/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalPrimeIntegralGenerators

/-!
# Exact original equations from localized integrality

Clear both coefficient denominators and target localization torsion. The
result is an equation in the unchanged target ring with leading coefficient
outside the original prime, without reducedness or injectivity assumptions.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OriginalPrimeIntegralFiber
open Polynomial
variable {R B : Type*} [CommRing R] [CommRing B]
  (s : R →+* B) (P : Ideal R) [P.IsPrime]
local notation "T" => Localization (P.primeCompl.map s)
local notation "L" => Localization.AtPrime P
local notation "τ" => localizedMap s P

/-- Normalizing a monic polynomial over the local ring retains a leading coefficient unit. -/
theorem integerNormalization_leadingCoeff_not_mem (p : L[X]) (hp : p.Monic) :
    (IsLocalization.integerNormalization P.primeCompl p).leadingCoeff ∉ P := by
  let q := IsLocalization.integerNormalization P.primeCompl p
  obtain ⟨a, ha, he⟩ := IsLocalization.integerNormalization_spec P.primeCompl p
  have hc : algebraMap R L (q.coeff p.natDegree) = algebraMap R L a := by
    rw [← IsScalarTower.algebraMap_smul L a p] at he
    have h := congrArg (fun r : L[X] ↦ r.coeff p.natDegree) he
    simpa only [coeff_map, coeff_smul, hp.coeff_natDegree, smul_eq_mul, mul_one] using h
  have hu : IsUnit (algebraMap R L a) := IsLocalization.map_units L ⟨a, ha⟩
  have hdeg : q.natDegree = p.natDegree := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro N hN
      apply notMem_support_iff.mp
      intro hq
      have hh := IsLocalization.integerNormalization_support P.primeCompl p hq
      exact (le_natDegree_of_mem_supp N hh).not_gt hN
    · intro hz
      exact hu.ne_zero (hc.symm.trans ((congrArg (algebraMap R L) hz).trans (map_zero _)))
  apply (IsLocalization.AtPrime.isUnit_to_map_iff L P _).mp
  change IsUnit (algebraMap R L (q.coeff q.natDegree))
  rw [hdeg, hc]
  exact hu

/-- A localized monic equation yields an exact original equation, including localization torsion. -/
theorem exists_equation_of_localized_integral (b : B)
    (hb : (τ).IsIntegralElem (algebraMap B T b)) :
    ∃ p : R[X], p.eval₂ s b = 0 ∧ p.leadingCoeff ∉ P := by
  obtain ⟨p, hp, he⟩ := hb
  let q := IsLocalization.integerNormalization P.primeCompl p
  have hq : q.leadingCoeff ∉ P := integerNormalization_leadingCoeff_not_mem P p hp
  have hzero : algebraMap B T (q.eval₂ s b) = 0 := by
    rw [hom_eval₂, ← localizedMap_comp]
    exact IsLocalization.integerNormalization_eval₂_eq_zero P.primeCompl τ p he
  obtain ⟨u, hu⟩ := (IsLocalization.map_eq_zero_iff (P.primeCompl.map s) T _).mp hzero
  obtain ⟨a, ha, hau⟩ := u.property
  have hn : a * q.leadingCoeff ∉ P := (inferInstance : P.IsPrime).mul_notMem ha hq
  have hne : a * q.leadingCoeff ≠ 0 := fun h ↦ hn (h ▸ P.zero_mem)
  refine ⟨C a * q, ?_, ?_⟩
  · rw [eval₂_mul, eval₂_C, hau]
    exact hu
  · rwa [leadingCoeff_mul' (by simpa only [leadingCoeff_C] using hne), leadingCoeff_C]

/-- Original leading-coefficient equations characterize integrality of a localized numerator. -/
theorem localized_integral_iff_equation (b : B) :
    (τ).IsIntegralElem (algebraMap B T b) ↔
      ∃ p : R[X], p.eval₂ s b = 0 ∧ p.leadingCoeff ∉ P := by
  refine ⟨exists_equation_of_localized_integral s P b, ?_⟩
  rintro ⟨p, hp, hlead⟩
  exact s.isIntegralElem_localization_at_leadingCoeff b p hp P.primeCompl hlead

/-- Local integrality is exactly the existence of original equations on any fixed generators. -/
theorem localizedMap_integral_iff_generator_equations (S : Set B)
    (hgen : Subring.closure (Set.range s ∪ S) = ⊤) :
    (τ).IsIntegral ↔
      ∀ b ∈ S, ∃ p : R[X], p.eval₂ s b = 0 ∧ p.leadingCoeff ∉ P := by
  refine ⟨fun h b _ ↦ exists_equation_of_localized_integral s P b (h _), ?_⟩
  exact localizedMap_integral_of_generator_equations s P S hgen

end FLT.Mazur.OriginalPrimeIntegralFiber

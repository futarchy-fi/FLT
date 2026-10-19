/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalLocalizationIntegralEquations
public import Mathlib.RingTheory.RingHom.FiniteType

/-!
# Whole finite algebras on original minimal-prime principal opens

Exact equations are multiplied by the other leading coefficients. All resulting
leading coefficients equal one product outside the original minimal prime.
Inverting that product makes the entire original algebra finite.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.QuasiFiniteMinimalPrimePrincipalAlgebra
open Polynomial
variable {R B : Type} [CommRing R] [CommRing B] [IsNoetherianRing R]
  (s : R →+* B) (P : PrimeSpectrum R)

omit [IsNoetherianRing R] in
/-- Finite type supplies actual finite original ring generators. -/
theorem exists_generators (hf : s.FiniteType) :
    ∃ S : Finset B, Subring.closure (Set.range s ∪ (S : Set B)) = ⊤ := by
  let _ := s.toAlgebra
  let _ : Algebra.FiniteType R B := hf
  obtain ⟨S, hS⟩ := Algebra.FiniteType.out (R := R) (A := B)
  refine ⟨S, ?_⟩
  change Subring.closure (Set.range (algebraMap R B) ∪ (S : Set B)) = ⊤
  rw [← Algebra.adjoin_eq_ring_closure, hS]
  rfl

/-- One original scalar makes the full principal localized map finite. -/
theorem exists_finite_principal
    (hP : P.asIdeal ∈ minimalPrimes R) (hs : s.QuasiFinite) (hf : s.FiniteType) :
    ∃ r : R, r ∉ P.asIdeal ∧
      (IsLocalization.Away.map (Localization.Away r) (Localization.Away (s r)) s r).Finite := by
  classical
  obtain ⟨S, hS⟩ := exists_generators s hf
  choose p hp hl using fun b : S ↦
    OriginalPrimeIntegralFiber.exists_equation_of_minimal_quasiFinite s P hP hs b.val
  let r := ∏ b : S, (p b).leadingCoeff
  have hr : r ∉ P.asIdeal := by
    intro h
    obtain ⟨b, _, hb⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hl b hb
  have hr0 : r ≠ 0 := fun h ↦ hr (h ▸ P.asIdeal.zero_mem)
  refine ⟨r, hr, ?_⟩
  let L := Localization.Away r
  let T := Localization.Away (s r)
  have hI : (IsLocalization.map T s (Submonoid.powers r).le_comap_map : L →+* T).IsIntegral := by
    apply OriginalLocalizationIntegralEquations.map_integral_of_generator_equations
      s (Submonoid.powers r) L T (S : Set B) hS
    intro b hb
    let i : S := ⟨b, hb⟩
    let a := ∏ j ∈ Finset.univ.erase i, (p j).leadingCoeff
    have ha : a * (p i).leadingCoeff = r :=
      Finset.prod_erase_mul _ _ (Finset.mem_univ i)
    refine ⟨C a * p i, ?_, ?_⟩
    · rw [eval₂_mul, eval₂_C, hp i, mul_zero]
    · rw [leadingCoeff_mul' (by simpa only [leadingCoeff_C, ha] using hr0),
        leadingCoeff_C, ha]
      exact Submonoid.mem_powers r
  apply hI.to_finite
  exact RingHom.finiteType_isStableUnderBaseChange.isLocalization_map
    (Submonoid.powers r) s hf

end FLT.Mazur.QuasiFiniteMinimalPrimePrincipalAlgebra

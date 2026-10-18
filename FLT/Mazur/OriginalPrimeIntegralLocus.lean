/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalPrimeIntegralEquations

/-!
# Spreading local integrality by constructed original equations

For a finite set of original scalar generators, integrality at one prime
constructs actual equations and a single product of leading coefficients.
The same equations prove integrality throughout that original principal open.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OriginalPrimeIntegralFiber
open Polynomial
variable {R B : Type*} [CommRing R] [CommRing B]
  (s : R →+* B) (G : Finset B)
  (hG : Subring.closure (Set.range s ∪ (G : Set B)) = ⊤)

/-- Local integrality constructs finitely many exact equations and one nonvanishing product. -/
theorem exists_finite_equations (P : Ideal R) [P.IsPrime]
    (h : (localizedMap s P).IsIntegral) :
    ∃ p : G → R[X],
      (∀ b : G, (p b).eval₂ s b.val = 0) ∧ (∏ b : G, (p b).leadingCoeff) ∉ P := by
  classical
  have hex (b : G) := exists_equation_of_localized_integral s P b.val (h _)
  choose p hp using hex
  refine ⟨p, fun b ↦ (hp b).1, ?_⟩
  intro hm
  obtain ⟨b, _, hb⟩ := Ideal.IsPrime.prod_mem_iff.mp hm
  exact (hp b).2 hb

include hG in
/-- The equations constructed at one prime prove integrality on a full original principal open. -/
theorem exists_principal_integral_neighborhood (P : PrimeSpectrum R)
    (h : (localizedMap s P.asIdeal).IsIntegral) :
    ∃ r : R, r ∉ P.asIdeal ∧ ∀ Q : PrimeSpectrum R,
      r ∉ Q.asIdeal → (localizedMap s Q.asIdeal).IsIntegral := by
  classical
  obtain ⟨p, hp, hprod⟩ := exists_finite_equations s G P.asIdeal h
  refine ⟨∏ b : G, (p b).leadingCoeff, hprod, fun Q hQ ↦ ?_⟩
  apply localizedMap_integral_of_generator_equations s Q.asIdeal (G : Set B) hG
  intro b hb
  refine ⟨p ⟨b, hb⟩, hp ⟨b, hb⟩, ?_⟩
  intro hm
  exact hQ (Ideal.IsPrime.prod_mem_iff.mpr ⟨⟨b, hb⟩, Finset.mem_univ _, hm⟩)

include hG in
/-- The original local-integrality locus of a finitely generated ring map is open. -/
theorem isOpen_localized_integral_locus :
    IsOpen {P : PrimeSpectrum R | (localizedMap s P.asIdeal).IsIntegral} := by
  apply isOpen_iff_mem_nhds.mpr
  intro P hP
  obtain ⟨r, hr, h⟩ := exists_principal_integral_neighborhood s G hG P hP
  exact Filter.mem_of_superset ((PrimeSpectrum.basicOpen r).isOpen.mem_nhds hr) h

end FLT.Mazur.OriginalPrimeIntegralFiber

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalPrimeIntegralNilpotents
public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Combining original equations on finite closed covers

Multiply equations for a finite family of quotients, then kill the nilpotent
error in their intersection. The original prime and scalar ring are retained.
This also treats an empty component family and the zero target ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OriginalPrimeIntegralFiber
open Polynomial
variable {R B : Type*} [CommRing R] [CommRing B]
  (s : R →+* B) (P : Ideal R) [P.IsPrime]
  {ι : Type*} [Finite ι] (I : ι → Ideal B)

/-- A product of component equations has nilpotent error and keeps its leading coefficient. -/
theorem exists_equation_of_component_equations
    (hI : (⨅ i, I i) ≤ nilradical B) (b : B) (p : ι → R[X])
    (he : ∀ i, (p i).eval₂ s b ∈ I i) (hp : ∀ i, (p i).leadingCoeff ∉ P) :
    ∃ q : R[X], q.eval₂ s b = 0 ∧ q.leadingCoeff ∉ P := by
  classical
  let _ := Fintype.ofFinite ι
  have hprod : (∏ i, (p i).leadingCoeff) ∉ P := by
    intro h
    obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hp i hi
  apply exists_equation_of_nilpotent_eval s P b (∏ i, p i)
  · apply mem_nilradical.mp
    apply hI
    rw [Submodule.mem_iInf]
    intro i
    rw [eval₂_finsetProd]
    exact (I i).prod_mem (Finset.mem_univ i) (he i)
  · rwa [leadingCoeff_prod' _ _ (fun h ↦ hprod (h ▸ P.zero_mem))]

/-- Localized component equations produce a single exact equation in the original target. -/
theorem exists_equation_of_component_integral
    (hI : (⨅ i, I i) ≤ nilradical B) (b : B)
    (h : ∀ i, (localizedMap ((Ideal.Quotient.mk (I i)).comp s) P).IsIntegral) :
    ∃ q : R[X], q.eval₂ s b = 0 ∧ q.leadingCoeff ∉ P := by
  classical
  have hex (i : ι) := exists_equation_of_localized_integral
    ((Ideal.Quotient.mk (I i)).comp s) P (Ideal.Quotient.mk (I i) b) (h i _)
  choose p hp using hex
  apply exists_equation_of_component_equations s P I hI b p _ (fun i ↦ (hp i).2)
  intro i
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [hom_eval₂]
  exact (hp i).1

/-- A finite closed cover detects integrality at the unchanged original prime. -/
theorem localizedMap_integral_iff_components (hI : (⨅ i, I i) ≤ nilradical B) :
    (localizedMap s P).IsIntegral ↔
      ∀ i, (localizedMap ((Ideal.Quotient.mk (I i)).comp s) P).IsIntegral := by
  refine ⟨fun h i ↦ localizedMap_integral_target_surjective s P _
    Ideal.Quotient.mk_surjective h, ?_⟩
  intro h
  apply localizedMap_integral_of_numerators
  intro b
  exact (localized_integral_iff_equation s P b).mpr
    (exists_equation_of_component_integral s P I hI b h)

/-- Failure of original local integrality has a component witness on every finite closed cover. -/
theorem exists_component_not_integral (hI : (⨅ i, I i) ≤ nilradical B)
    (h : ¬ (localizedMap s P).IsIntegral) :
    ∃ i, ¬ (localizedMap ((Ideal.Quotient.mk (I i)).comp s) P).IsIntegral := by
  classical
  simpa only [not_forall] using h.imp (localizedMap_integral_iff_components s P I hI).mpr

end FLT.Mazur.OriginalPrimeIntegralFiber

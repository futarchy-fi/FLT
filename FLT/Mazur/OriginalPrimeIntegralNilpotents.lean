/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalPrimeIntegralEquations

/-!
# Recovering original equations from nilpotent errors

A power kills a nilpotent evaluation error without moving the original prime.
Consequently local integrality can be checked after any nil ideal quotient,
while the resulting equations hold in the original, possibly nonreduced ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OriginalPrimeIntegralFiber
open Polynomial
variable {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
  (s : R →+* B) (P : Ideal R) [P.IsPrime]

/-- A nilpotent equation error is removed by a power whose leading coefficient still avoids P. -/
theorem exists_equation_of_nilpotent_eval (b : B) (p : R[X])
    (he : IsNilpotent (p.eval₂ s b)) (hp : p.leadingCoeff ∉ P) :
    ∃ q : R[X], q.eval₂ s b = 0 ∧ q.leadingCoeff ∉ P := by
  obtain ⟨n, hn⟩ := he
  have hpn : p.leadingCoeff ^ n ∉ P := fun h ↦ hp ((inferInstance : P.IsPrime).mem_of_pow_mem _ h)
  refine ⟨p ^ n, ?_, ?_⟩
  · rwa [eval₂_pow]
  · rwa [leadingCoeff_pow' (fun h ↦ hpn (h ▸ P.zero_mem))]

/-- Local integrality descends along any surjective target map at the same original prime. -/
theorem localizedMap_integral_target_surjective (t : B →+* C) (ht : Function.Surjective t)
    (h : (localizedMap s P).IsIntegral) : (localizedMap (t.comp s) P).IsIntegral := by
  apply localizedMap_integral_of_numerators
  intro c
  obtain ⟨b, rfl⟩ := ht c
  obtain ⟨p, hp, hlead⟩ := exists_equation_of_localized_integral s P b (h _)
  apply (localized_integral_iff_equation (t.comp s) P (t b)).mpr
  refine ⟨p, ?_, hlead⟩
  rw [← hom_eval₂, hp, map_zero]

/-- Equations modulo a nil ideal lift to exact equations in the original target ring. -/
theorem exists_equation_of_nil_quotient (I : Ideal B) (hI : I ≤ nilradical B) (b : B)
    (h : (localizedMap ((Ideal.Quotient.mk I).comp s) P).IsIntegralElem
      (algebraMap (B ⧸ I) (Localization (P.primeCompl.map ((Ideal.Quotient.mk I).comp s)))
        (Ideal.Quotient.mk I b))) :
    ∃ p : R[X], p.eval₂ s b = 0 ∧ p.leadingCoeff ∉ P := by
  obtain ⟨p, hp, hlead⟩ := exists_equation_of_localized_integral
    ((Ideal.Quotient.mk I).comp s) P (Ideal.Quotient.mk I b) h
  apply exists_equation_of_nilpotent_eval s P b p _ hlead
  apply mem_nilradical.mp
  apply hI
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rwa [hom_eval₂]

/-- Nil ideal quotients detect local integrality without discarding original nilpotents. -/
theorem localizedMap_integral_iff_nil_quotient (I : Ideal B) (hI : I ≤ nilradical B) :
    (localizedMap s P).IsIntegral ↔
      (localizedMap ((Ideal.Quotient.mk I).comp s) P).IsIntegral := by
  refine ⟨localizedMap_integral_target_surjective s P _ (Ideal.Quotient.mk_surjective), ?_⟩
  intro h
  apply localizedMap_integral_of_numerators
  intro b
  exact (localized_integral_iff_equation s P b).mpr
    (exists_equation_of_nil_quotient s P I hI b (h _))

/-- The reduction of the target suffices; the scalar ring and prime are unchanged. -/
theorem localizedMap_integral_iff_reduction :
    (localizedMap s P).IsIntegral ↔
      (localizedMap ((Ideal.Quotient.mk (nilradical B)).comp s) P).IsIntegral :=
  localizedMap_integral_iff_nil_quotient s P (nilradical B) le_rfl

end FLT.Mazur.OriginalPrimeIntegralFiber

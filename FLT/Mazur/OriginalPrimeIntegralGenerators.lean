/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalPrimeIntegralFiber

/-!
# Constructing local integrality from generator equations

Polynomial equations whose leading coefficients avoid the original prime
make the localized generator images integral. Ring generation and clearing
fractions then prove integrality of the entire localized scalar map.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OriginalPrimeIntegralFiber
open Polynomial
variable {R B : Type*} [CommRing R] [CommRing B]
  (s : R →+* B) (P : Ideal R) [P.IsPrime]
local notation "T" => Localization (P.primeCompl.map s)
local notation "L" => Localization.AtPrime P
local notation "τ" => localizedMap s P

/-- It suffices to prove integrality for the images of unlocalized numerators. -/
theorem localizedMap_integral_of_numerators
    (h : ∀ b : B, (τ).IsIntegralElem (algebraMap B T b)) : (τ).IsIntegral := by
  intro x
  obtain ⟨⟨b, u⟩, hx⟩ := IsLocalization.surj (P.primeCompl.map s) x
  obtain ⟨a, ha, he⟩ := u.property
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv'.mp (IsLocalization.map_units L ⟨a, ha⟩)
  have hv' : τ v * algebraMap B T u.val = 1 := by
    have hh := congrArg τ hv
    rw [map_mul, map_one] at hh
    have heq : τ (algebraMap R L a) = algebraMap B T (s a) :=
      congrArg (fun f : R →+* T ↦ f a) (localizedMap_comp s P)
    rwa [heq, he] at hh
  exact RingHom.IsIntegralElem.of_mul_unit τ x (algebraMap B T u.val) v hv'
    (hx.symm ▸ h b)

/-- Polynomial tests on algebra generators construct integrality at the original prime. -/
theorem localizedMap_integral_of_generator_equations (S : Set B)
    (hgen : Subring.closure (Set.range s ∪ S) = ⊤)
    (heq : ∀ b ∈ S, ∃ p : R[X], p.eval₂ s b = 0 ∧ p.leadingCoeff ∉ P) :
    (τ).IsIntegral := by
  apply localizedMap_integral_of_numerators
  intro b
  have hb : b ∈ Subring.closure (Set.range s ∪ S) := hgen ▸ Subring.mem_top b
  induction hb using Subring.closure_induction with
  | mem b hb =>
    rcases hb with ⟨r, rfl⟩ | hb
    · have h := (τ).isIntegralElem_map (x := algebraMap R L r)
      have he := congrArg (fun f : R →+* T ↦ f r) (localizedMap_comp s P)
      change τ (algebraMap R L r) = algebraMap B T (s r) at he
      rwa [he] at h
    · obtain ⟨p, hp, hlead⟩ := heq b hb
      exact s.isIntegralElem_localization_at_leadingCoeff b p hp P.primeCompl hlead
  | zero => simpa only [map_zero] using (τ).isIntegralElem_map (x := 0)
  | one => simpa only [map_one] using (τ).isIntegralElem_map (x := 1)
  | add x y _ _ hx hy => simpa only [map_add] using hx.add τ hy
  | neg x _ hx => simpa only [map_neg] using hx.neg
  | mul x y _ _ hx hy => simpa only [map_mul] using hx.mul τ hy

/-- Generator equations and an empty fiber give a scalar killing the exact target ring. -/
theorem exists_kernel_scalar_of_generator_equations (S : Set B)
    (hgen : Subring.closure (Set.range s ∪ S) = ⊤)
    (heq : ∀ b ∈ S, ∃ p : R[X], p.eval₂ s b = 0 ∧ p.leadingCoeff ∉ P)
    (hP : ∀ Q : PrimeSpectrum B, Q.asIdeal.comap s ≠ P) :
    ∃ r : R, r ∉ P ∧ s r = 0 :=
  exists_kernel_scalar s P (localizedMap_integral_of_generator_equations s P S hgen heq) hP

/-- One explicit product controls local integrality for a finite algebra presentation. -/
theorem localizedMap_integral_of_finite_equations {I : Type*} [Fintype I]
    (b : I → B) (p : I → R[X])
    (hgen : Subring.closure (Set.range s ∪ Set.range b) = ⊤)
    (heq : ∀ i, (p i).eval₂ s (b i) = 0)
    (hP : (∏ i, (p i).leadingCoeff) ∉ P) : (τ).IsIntegral := by
  apply localizedMap_integral_of_generator_equations s P (Set.range b) hgen
  rintro _ ⟨i, rfl⟩
  refine ⟨p i, heq i, ?_⟩
  intro hi
  apply hP
  exact Ideal.IsPrime.prod_mem_iff.mpr ⟨i, Finset.mem_univ i, hi⟩

end FLT.Mazur.OriginalPrimeIntegralFiber

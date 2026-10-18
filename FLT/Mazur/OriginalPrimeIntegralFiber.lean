/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Empty fibers for maps integral at the original prime

Only the localized map must be integral. An empty fiber then kills the
localized target ring, producing an original scalar outside the prime in
the exact kernel. No global integrality or reduction is required.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OriginalPrimeIntegralFiber
variable {R B : Type*} [CommRing R] [CommRing B]
  (s : R →+* B) (P : Ideal R) [P.IsPrime]

/-- Localize both rings using precisely the complement of the original prime. -/
def localizedMap : Localization.AtPrime P →+* Localization (P.primeCompl.map s) :=
  IsLocalization.map (M := P.primeCompl) (T := P.primeCompl.map s)
    (Localization (P.primeCompl.map s)) s (fun _ hr ↦ ⟨_, hr, rfl⟩)

/-- The localized map retains the original scalar square. -/
theorem localizedMap_comp :
    (localizedMap s P).comp (algebraMap R (Localization.AtPrime P)) =
      (algebraMap B (Localization (P.primeCompl.map s))).comp s :=
by
  unfold localizedMap
  exact IsLocalization.map_comp _

/-- Local integrality and an empty original fiber give an exact kernel denominator. -/
theorem exists_kernel_scalar
    (hInt : (localizedMap s P).IsIntegral)
    (hP : ∀ Q : PrimeSpectrum B, Q.asIdeal.comap s ≠ P) :
    ∃ r : R, r ∉ P ∧ s r = 0 := by
  let T := Localization (P.primeCompl.map s)
  have hzero : (1 : T) = 0 := by
    by_contra hn
    let _ : Nontrivial T := nontrivial_of_ne 1 0 hn
    obtain ⟨Q, hQ⟩ := Ideal.exists_maximal (α := T)
    let _ := hQ
    have hmax : Q.comap (localizedMap s P) =
        IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _ hInt Q)
    let q : PrimeSpectrum B := PrimeSpectrum.comap (algebraMap B T) ⟨Q, hQ.isPrime⟩
    apply hP q
    change (Q.comap (algebraMap B T)).comap s = P
    rw [Ideal.comap_comap, ← localizedMap_comp s P, ← Ideal.comap_comap, hmax]
    exact Localization.AtPrime.under_maximalIdeal
  have hz : algebraMap B T 1 = 0 := (map_one _).trans hzero
  obtain ⟨r, hr⟩ := (IsLocalization.map_eq_zero_iff (P.primeCompl.map s) T 1).mp hz
  obtain ⟨a, ha, he⟩ := r.property
  exact ⟨a, ha, by simpa only [mul_one, ← he] using hr⟩

/-- The local integrality input includes every globally integral scalar map. -/
theorem localizedMap_isIntegral (h : s.IsIntegral) : (localizedMap s P).IsIntegral :=
  isIntegral_localization' h P.primeCompl

/-- Under local integrality, fiber emptiness is equivalent to exact original kernel avoidance. -/
theorem empty_fiber_iff (hInt : (localizedMap s P).IsIntegral) :
    (∀ Q : PrimeSpectrum B, Q.asIdeal.comap s ≠ P) ↔
      ∃ r : R, r ∉ P ∧ s r = 0 := by
  refine ⟨exists_kernel_scalar s P hInt, ?_⟩
  rintro ⟨r, hr, hz⟩ Q hQ
  apply hr
  rw [← hQ]
  change s r ∈ Q.asIdeal
  rw [hz]
  exact Q.asIdeal.zero_mem

end FLT.Mazur.OriginalPrimeIntegralFiber

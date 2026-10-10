/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Simultaneous projective neighborhoods for finite cohomology modules

A finite collection of finitely presented modules, free at a chosen prime,
is simultaneously projective on one principal neighborhood. Over a domain,
the generic point always satisfies the required freeness.
-/

@[expose] public noncomputable section

open TopologicalSpace PrimeSpectrum
namespace FLT.Mazur.Approximation

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
  (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, Module.FinitePresentation R (M i)]

/-- One principal neighborhood makes finitely many stalkwise free modules projective. -/
theorem exists_simultaneous_projective_neighborhood (p : PrimeSpectrum R)
    (hp : ∀ i, p ∈ Module.freeLocus R (M i)) :
    ∃ r ∉ p.asIdeal, ∀ i,
      Module.Projective (Localization.Away r) (LocalizedModule.Away r (M i)) := by
  let U : Opens (PrimeSpectrum R) :=
    ⟨⋂ i, Module.freeLocus R (M i), isOpen_iInter_of_finite fun i ↦ Module.isOpen_freeLocus⟩
  have hpU : p ∈ U := Set.mem_iInter.mpr hp
  obtain ⟨V, ⟨r, rfl⟩, hpr, hrU⟩ :=
    Opens.isBasis_iff_nbhd.mp isBasis_basic_opens hpU
  refine ⟨r, hpr, fun i ↦ Module.basicOpen_subset_freeLocus_iff.mp ?_⟩
  intro q hq
  exact Set.mem_iInter.mp (hrU hq) i

omit [Finite ι] [∀ i, Module.FinitePresentation R (M i)] in
/-- A finite module over a domain is free at the generic point. -/
theorem genericPoint_mem_freeLocus [IsDomain R] (i : ι) :
    (⟨⊥, inferInstance⟩ : PrimeSpectrum R) ∈ Module.freeLocus R (M i) := by
  change Module.Free (Localization.AtPrime (⊥ : Ideal R))
    (LocalizedModule.AtPrime (⊥ : Ideal R) (M i))
  change Module.Free (Localization ((⊥ : Ideal R).primeCompl))
    (LocalizedModule ((⊥ : Ideal R).primeCompl) (M i))
  rw [Ideal.primeCompl_bot]
  infer_instance

/-- Finite collections of finitely presented modules are projective on a common dense open. -/
theorem exists_simultaneous_generic_projective [IsDomain R] :
    ∃ r : R, r ≠ 0 ∧ ∀ i,
      Module.Projective (Localization.Away r) (LocalizedModule.Away r (M i)) := by
  obtain ⟨r, hr, hM⟩ := exists_simultaneous_projective_neighborhood (R := R) M
    ⟨⊥, inferInstance⟩ (genericPoint_mem_freeLocus M)
  exact ⟨r, by simpa using hr, hM⟩

end FLT.Mazur.Approximation

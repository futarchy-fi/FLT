/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! # Faithful covering across a nilpotent thickening

Flatness of the lifted algebra is an input here. This theorem proves the covering
condition; it does not assert existence or flatness of a lifted presentation.
-/

@[expose] public noncomputable section
namespace PrimeSpectrum
variable {B C : Type*} [CommRing B] [CommRing C]

/-- A surjection with elementwise nilpotent kernel is surjective on spectra. -/
theorem comap_surjective_of_nilpotent_kernel (q : B →+* C)
    (hq : Function.Surjective q) (hnil : ∀ b ∈ RingHom.ker q, IsNilpotent b) :
    Function.Surjective (comap q) := by
  intro P
  have hker : RingHom.ker q ≤ P.asIdeal := by
    intro b hb
    obtain ⟨n, hn⟩ := hnil b hb
    exact P.isPrime.mem_of_pow_mem n (hn ▸ P.asIdeal.zero_mem)
  exact (show P ∈ Set.range (comap q) by
    rw [range_comap_of_surjective C q hq]
    exact hker)

end PrimeSpectrum
namespace Module.FaithfullyFlat
variable {B C D E : Type*} [CommRing B] [CommRing C] [CommRing D] [CommRing E]
  [Algebra B D] [Algebra C E]

/-- A flat lift is faithfully flat if a nilpotent reduction admits a faithfully flat cover
mapping from that lift. The map from the lift to the reduced cover need not be surjective. -/
theorem of_nilpotent_cover_square [Flat B D] [FaithfullyFlat C E]
    (q : B →+* C) (hq : Function.Surjective q)
    (hnil : ∀ b ∈ RingHom.ker q, IsNilpotent b) (t : D →+* E)
    (hcomm : t.comp (algebraMap B D) = (algebraMap C E).comp q) :
    FaithfullyFlat B D := by
  apply of_comap_surjective
  intro P
  obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_nilpotent_kernel q hq hnil P
  obtain ⟨U, hU⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := C) (B := E) Q
  refine ⟨PrimeSpectrum.comap t U, ?_⟩
  have he : PrimeSpectrum.comap (algebraMap B D) (PrimeSpectrum.comap t U) =
      PrimeSpectrum.comap q (PrimeSpectrum.comap (algebraMap C E) U) := by
    change PrimeSpectrum.comap (t.comp (algebraMap B D)) U =
      PrimeSpectrum.comap ((algebraMap C E).comp q) U
    rw [hcomm]
  rw [he, hU, hQ]

end Module.FaithfullyFlat

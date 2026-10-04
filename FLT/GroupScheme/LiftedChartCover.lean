/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.NilpotentCovering
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Assembling flat lifted charts into a faithfully flat cover

Flatness of every lifted chart is required. Joint surjectivity is proved from the
reduced charts, including the case of principal charts of the actual division algebra.
-/

@[expose] public noncomputable section
namespace Module.FaithfullyFlat
variable {B C : Type*} [CommRing B] [CommRing C]
  {ι : Type*} [Finite ι] (D E : ι → Type*)
  [∀ i, CommRing (D i)] [∀ i, CommRing (E i)]
  [∀ i, Algebra B (D i)] [∀ i, Algebra C (E i)] [∀ i, Flat B (D i)]

/-- Finitely many flat lifted charts form a faithfully flat algebra if their reductions
jointly cover a nilpotent quotient of the base. -/
theorem pi_of_nilpotent_cover_charts (q : B →+* C) (hq : Function.Surjective q)
    (hnil : ∀ b ∈ RingHom.ker q, IsNilpotent b)
    (t : ∀ i, D i →+* E i)
    (hcomm : ∀ i, (t i).comp (algebraMap B (D i)) = (algebraMap C (E i)).comp q)
    (hcover : ∀ Q : PrimeSpectrum C, ∃ i, ∃ U : PrimeSpectrum (E i),
      PrimeSpectrum.comap (algebraMap C (E i)) U = Q) :
    FaithfullyFlat B (∀ i, D i) := by
  let : Fintype ι := Fintype.ofFinite ι
  let : Flat B (∀ i, D i) :=
    Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := B) (M := D)).symm
  apply of_comap_surjective
  intro P
  obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_nilpotent_kernel q hq hnil P
  obtain ⟨i, U, hU⟩ := hcover Q
  refine ⟨PrimeSpectrum.comap ((t i).comp (Pi.evalRingHom D i)) U, ?_⟩
  change PrimeSpectrum.comap
    (((t i).comp (Pi.evalRingHom D i)).comp (algebraMap B (∀ i, D i))) U = P
  have he : ((t i).comp (Pi.evalRingHom D i)).comp (algebraMap B (∀ i, D i)) =
      (algebraMap C (E i)).comp q := hcomm i
  rw [he]
  change PrimeSpectrum.comap q (PrimeSpectrum.comap (algebraMap C (E i)) U) = P
  rw [hU, hQ]

end Module.FaithfullyFlat
namespace PrimeSpectrum
variable {C E : Type*} [CommRing C] [CommRing E] [Algebra C E]
  [Module.FaithfullyFlat C E] {ι : Type*} (s : ι → E)

/-- Principal charts whose defining elements generate the unit ideal jointly cover the base
of a faithfully flat algebra. -/
theorem localization_charts_cover (hs : Ideal.span (Set.range s) = ⊤) :
    ∀ Q : PrimeSpectrum C, ∃ i, ∃ U : PrimeSpectrum (Localization.Away (s i)),
      comap (algebraMap C (Localization.Away (s i))) U = Q := by
  intro Q
  obtain ⟨P, hP⟩ := comap_surjective_of_faithfullyFlat (A := C) (B := E) Q
  have hex : ∃ i, s i ∉ P.asIdeal := by
    by_contra! h
    have hle : Ideal.span (Set.range s) ≤ P.asIdeal := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact h i
    rw [hs, top_le_iff] at hle
    exact P.isPrime.ne_top hle
  obtain ⟨i, hi⟩ := hex
  have hm : P ∈ Set.range (comap (algebraMap E (Localization.Away (s i)))) := by
    rw [localization_away_comap_range (Localization.Away (s i)) (s i)]
    exact hi
  obtain ⟨U, hU⟩ := hm
  refine ⟨i, U, ?_⟩
  rw [IsScalarTower.algebraMap_eq C E (Localization.Away (s i))]
  change comap (algebraMap C E) (comap (algebraMap E (Localization.Away (s i))) U) = Q
  rw [hU, hP]

end PrimeSpectrum

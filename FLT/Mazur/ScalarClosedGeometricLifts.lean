/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarAlgebraicClosureTests
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Original scalar characters on closed affine loci

Every scalar prime reached by a closed locus has a point on that locus over
its own residue closure. Quotienting the source equations preserves finite
type and the full scalar character; no residue-field embedding is assumed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarTestLocalization
variable {R B : Type} [CommRing R] [CommRing B]
  (s : R →+* B) (hs : s.FiniteType) (J : Ideal B) (P : PrimeSpectrum R)
local notation "K" => AlgebraicClosure P.asIdeal.ResidueField

include hs in
/-- Construct an exact original scalar character satisfying every closed-source equation. -/
theorem exists_scalar_character_on_closed (q : PrimeSpectrum B)
    (hq : PrimeSpectrum.comap s q = P) (hJ : J ≤ q.asIdeal) :
    ∃ w : B →+* K, w.comp s = algebraMap R K ∧ ∀ b ∈ J, w b = 0 := by
  let π := Ideal.Quotient.mk J
  have hr : q ∈ Set.range (PrimeSpectrum.comap π) := by
    rw [range_comap_of_surjective _ π Ideal.Quotient.mk_surjective]
    simpa only [π, Ideal.mk_ker, PrimeSpectrum.mem_zeroLocus,
      SetLike.coe_subset_coe] using hJ
  obtain ⟨q', he⟩ := hr
  have ht : (π.comp s).FiniteType :=
    (RingHom.FiniteType.of_surjective π Ideal.Quotient.mk_surjective).comp hs
  have hq' : PrimeSpectrum.comap (π.comp s) q' = P := by
    rw [PrimeSpectrum.comap_comp, Function.comp_apply, he, hq]
  obtain ⟨v, hv, _⟩ := exists_residue_geometric_failure (π.comp s) P ht 1 q' hq'
    q'.isPrime.one_notMem
  refine ⟨v.comp π, ?_, ?_⟩
  · exact hv
  · intro b hb
    change v (Ideal.Quotient.mk J b) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]

end FLT.Mazur.ScalarTestLocalization

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeTranslationNormFiber
public import FLT.Mazur.AffineEnvelopeFiniteNeighborhood
public import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Constructed norm neighborhoods inside finite translation envelopes

Prime avoidance on the entire finite fiber supplies an envelope coefficient.
Its genuine finite-free norm is nonzero at the chosen source point and cuts
out a source principal open whose whole envelope lies in the prescribed open.
No invariance of the chosen envelope coefficient or its norm is asserted.
-/

@[expose] public noncomputable section
open Module TopologicalSpace
namespace FLT.Mazur.FiniteFreeTranslationNorm
universe u v w
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {ι : Type w} [Finite ι] (b : Basis ι R S)
include b

/-- Every point over a norm principal open lies in the coefficient principal open. -/
theorem preimage_basicOpen_norm_le (s : S) :
    PrimeSpectrum.comap (algebraMap R S) ⁻¹' (PrimeSpectrum.basicOpen (Algebra.norm R s) :
      Set (PrimeSpectrum R)) ⊆ PrimeSpectrum.basicOpen s := by
  intro q hq
  exact (mem_basicOpen_norm_iff b _ s).mp hq q rfl

/-- Norms construct principal neighborhoods whose entire original envelope stays in an open. -/
theorem exists_norm_neighborhood (p : PrimeSpectrum R) (U : Opens (PrimeSpectrum S))
    (hU : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} ⊆ U) :
    ∃ s : S, p ∈ PrimeSpectrum.basicOpen (Algebra.norm R s) ∧
      PrimeSpectrum.basicOpen s ≤ U ∧
      PrimeSpectrum.comap (algebraMap R S) ⁻¹'
        (PrimeSpectrum.basicOpen (Algebra.norm R s) : Set (PrimeSpectrum R)) ⊆ U := by
  let _ := Fintype.ofFinite ι
  let _ := Module.Finite.of_basis b
  obtain ⟨s, hs, hsU⟩ := AffineEnvelopeFiniteNeighborhood.exists_principal U
    (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})
    (Algebra.QuasiFinite.finite_comap_preimage_singleton p) hU
  refine ⟨s, (mem_basicOpen_norm_iff b p s).mpr (fun q hq ↦ hs hq), hsU, ?_⟩
  exact (preimage_basicOpen_norm_le b s).trans hsU

/-- The full-fiber locus is covered by constructed norm principal opens. -/
theorem fullFiber_eq_union_norm (U : Opens (PrimeSpectrum S)) :
    {p : PrimeSpectrum R | PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} ⊆ U} =
      ⋃ s : {s : S // PrimeSpectrum.basicOpen s ≤ U},
        (PrimeSpectrum.basicOpen (Algebra.norm R s.val) : Set (PrimeSpectrum R)) := by
  ext p
  constructor
  · intro hp
    obtain ⟨s, hs, hsU, _⟩ := exists_norm_neighborhood b p U hp
    exact Set.mem_iUnion.mpr ⟨⟨s, hsU⟩, hs⟩
  · intro hp q hq
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hp
    exact s.property ((mem_basicOpen_norm_iff b p s.val).mp hs q hq)

end FLT.Mazur.FiniteFreeTranslationNorm

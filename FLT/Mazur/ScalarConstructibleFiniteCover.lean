/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# Finite subcovers of actual constructible scalar images

The constructible topology makes constructible scalar pieces open and closed.
Its compactness turns a cover of an actual constructible scalar image into a
finite subcover, without replacing the image by its Zariski closure.
-/

@[expose] public noncomputable section
open TopologicalSpace Topology
namespace FLT.Mazur.ScalarConstructibleStrata
variable {R : Type} [CommRing R]

/-- Constructible covers of a constructible scalar set have finite subcovers. -/
theorem exists_finite_constructible_subcover {ι : Type*}
    (Z : Set (PrimeSpectrum R)) (hZ : IsConstructible Z)
    (U : ι → Set (PrimeSpectrum R)) (hU : ∀ i, IsConstructible (U i))
    (hcover : Z ⊆ ⋃ i, U i) :
    ∃ J : Finset ι, Z ⊆ ⋃ i ∈ J, U i := by
  let v : WithConstructibleTopology (PrimeSpectrum R) → PrimeSpectrum R := WithTopology.ofTopology
  have hop (S : Set (PrimeSpectrum R)) (hS : IsConstructible S) : IsOpen (v ⁻¹' S) := by
    rw [WithConstructibleTopology.isOpen_iff]
    change IsOpen[constructibleTopology (PrimeSpectrum R)] S
    rw [constructibleTopology_eq_generateFrom_isConstructible]
    exact isOpen_generateFrom_of_mem hS
  have hz : IsClosed (v ⁻¹' Z) := by
    simpa only [Set.preimage_compl, compl_compl] using (hop Zᶜ hZ.compl).isClosed_compl
  obtain ⟨J, hJ⟩ := hz.isCompact.elim_finite_subcover (fun i ↦ v ⁻¹' U i)
    (fun i ↦ hop _ (hU i)) (by
      simpa only [Set.preimage_iUnion] using Set.preimage_mono (f := v) hcover)
  refine ⟨J, fun x hx ↦ ?_⟩
  have h := hJ (show WithTopology.toTopology _ x ∈ v ⁻¹' Z from hx)
  simpa only [Set.mem_iUnion, Set.mem_preimage, v, WithTopology.ofTopology_toTopology] using h

end FLT.Mazur.ScalarConstructibleStrata

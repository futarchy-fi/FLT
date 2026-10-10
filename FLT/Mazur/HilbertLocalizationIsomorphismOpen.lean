/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The open locus of an isomorphism of finitely presented modules

An isomorphism after prime localization spreads to a principal neighborhood.
This constructs an intrinsic open without choosing module trivializations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]

/-- A localized isomorphism remains an isomorphism when more scalars are inverted. -/
theorem localizedMap_bijective_of_le (S T : Submonoid R) (h : S ≤ T) (l : M →ₗ[R] N)
    (hl : Function.Bijective (LocalizedModule.map S l)) :
    Function.Bijective (LocalizedModule.map T l) := by
  let f := LocalizedModule.liftOfLE (M := M) S T h
  let g := LocalizedModule.liftOfLE (M := N) S T h
  let lS := (LocalizedModule.map S l).restrictScalars R
  have hi := IsLocalizedModule.map_injective T f g lS hl.1
  have hs := IsLocalizedModule.map_surjective T f g lS hl.2
  have he : IsLocalizedModule.map T f g lS =
      (LocalizedModule.map T l).restrictScalars R := by
    apply IsLocalizedModule.ext T (LocalizedModule.mkLinearMap T M)
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap T N))
    ext m
    change IsLocalizedModule.map T f g lS (LocalizedModule.mkLinearMap T M m) = _
    rw [← IsLocalizedModule.liftOfLE_apply S T h (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap T M) m]
    rw [IsLocalizedModule.map_apply]
    simpa only [lS, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LocalizedModule.mkLinearMap_apply,
      LocalizedModule.map_mk] using
      IsLocalizedModule.liftOfLE_apply S T h (LocalizedModule.mkLinearMap S N)
        (LocalizedModule.mkLinearMap T N) (l m)
  rw [he] at hi hs
  exact ⟨hi, hs⟩

/-- The intrinsic prime-local isomorphism locus. -/
def localIsomorphismLocus (l : M →ₗ[R] N) : Set (PrimeSpectrum R) :=
  {p | Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl l)}

/-- The locus is open for finite source and finitely presented target. -/
theorem isOpen_localIsomorphismLocus [Module.Finite R M] [Module.FinitePresentation R N]
    (l : M →ₗ[R] N) : IsOpen (localIsomorphismLocus l) := by
  refine isOpen_iff_forall_mem_open.mpr fun p hp ↦ ?_
  have hp' : Function.Bijective (IsLocalizedModule.map p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N) l) := hp
  obtain ⟨r, hr, hb⟩ := Module.FinitePresentation.exists_notMem_bijective l p.asIdeal
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N) hp'
  refine ⟨PrimeSpectrum.basicOpen r, ?_, (PrimeSpectrum.basicOpen r).isOpen, hr⟩
  intro q hq
  exact localizedMap_bijective_of_le (.powers r) q.asIdeal.primeCompl
    (Submonoid.powers_le.mpr hq) l hb

end FLT.Mazur.HilbertChart

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Canonical flat branches above original scalar primes

Localizing the original scalar ring at each of its primes constructs a flat
branch and a distinguished prime above it. Extension of the whole ideal has
exactly the original vanishing test at that distinguished prime.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarPrimeLocalizationCover
variable {R : Type} [CommRing R] (x : PrimeSpectrum R)

/-- The canonical flat branch retains the original scalar ring as its base. -/
def Branch := Localization.AtPrime x.asIdeal

/-- Cache the actual localization ring operations before specializing the original scalars. -/
instance branchCommRing : CommRing (Branch x) :=
  inferInstanceAs (CommRing (Localization.AtPrime x.asIdeal))

/-- The scalar map is the original localization map. -/
instance branchAlgebra : Algebra R (Branch x) :=
  inferInstanceAs (Algebra R (Localization.AtPrime x.asIdeal))

/-- The full localization universal property survives sealing the carrier. -/
instance branchLocalization : IsLocalization.AtPrime (Branch x) x.asIdeal :=
  inferInstanceAs (IsLocalization.AtPrime (Localization.AtPrime x.asIdeal) x.asIdeal)

/-- The distinguished branch retains its local ring structure. -/
instance branchLocalRing : IsLocalRing (Branch x) :=
  inferInstanceAs (IsLocalRing (Localization.AtPrime x.asIdeal))

/-- Flatness is cached before specializing to the original invariant ring. -/
instance branchFlat : Module.Flat R (Branch x) :=
  inferInstanceAs (Module.Flat R (Localization.AtPrime x.asIdeal))

attribute [irreducible] Branch

/-- Its distinguished prime is the maximal ideal, not a residue-field replacement. -/
def point : PrimeSpectrum (Branch x) :=
  ⟨IsLocalRing.maximalIdeal (Branch x), inferInstance⟩

/-- Every original prime is covered by its constructed flat localization. -/
theorem point_comap :
    (point x).asIdeal.comap (algebraMap R (Branch x)) = x.asIdeal :=
  IsLocalization.AtPrime.under_maximalIdeal _ _

/-- The distinguished branch point lies over the literal original point. -/
theorem comap_point : PrimeSpectrum.comap (algebraMap R (Branch x)) (point x) = x :=
  PrimeSpectrum.ext (point_comap x)

/-- The branch algebra is flat without any finiteness assumption. -/
theorem branch_flat : Module.Flat R (Branch x) := inferInstance

/-- Testing an extended whole ideal at this branch point loses no original equations. -/
theorem point_mem_zeroLocus_map_iff (Q : Ideal R) :
    point x ∈ PrimeSpectrum.zeroLocus
      (Q.map (algebraMap R (Branch x)) : Set (Branch x)) ↔
      x ∈ PrimeSpectrum.zeroLocus (Q : Set R) := by
  change Q.map (algebraMap R (Branch x)) ≤ (point x).asIdeal ↔ Q ≤ x.asIdeal
  rw [Ideal.map_le_iff_le_comap, point_comap]

end FLT.Mazur.ScalarPrimeLocalizationCover

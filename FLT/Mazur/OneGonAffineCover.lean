/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BinaryOpenDescent
public import FLT.Mazur.OneGonGluing
public import FLT.Mazur.ProjectiveLineCharts

/-!
# An affine cover for the one-gon normalization

The principal opens D(X-1) and D(X) cover the affine line. Their intersection
is the existing puncture ring, with its ordinary (untransformed) coordinate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open scoped LaurentPolynomial

universe u

namespace FLT.Mazur.OneGonAffineCover

open OneGonTransition

variable (K : Type u) [Field K]

/-- Functions on the affine line with one removed. -/
abbrev awayOne := Localization.Away (X - 1 : K[X])

/-- Inclusion of D(X-1) into the affine line. -/
def openOne : Spec (.of (awayOne K)) ⟶ ProjectiveLine.chart K :=
  Spec.map (CommRingCat.ofHom (algebraMap K[X] (awayOne K)))

instance : IsOpenImmersion (openOne K) :=
  IsOpenImmersion.of_isLocalization (X - 1 : K[X])

/-- Restriction from D(X-1) to D(X(X-1)). -/
def restrictOne : awayOne K →+* puncture K :=
  IsLocalization.Away.lift (X - 1 : K[X])
    (g := algebraMap K[X] (puncture K)) (by simpa using (difference K).isUnit)

@[simp]
theorem restrictOne_algebraMap (p : K[X]) :
    restrictOne K (algebraMap K[X] (awayOne K) p) = algebraMap K[X] (puncture K) p := by
  exact IsLocalization.Away.lift_eq (X - 1 : K[X])
    (by simpa using (difference K).isUnit) p

/-- Inclusion of the intersection into D(X-1). -/
def toOne : Spec (.of (puncture K)) ⟶ Spec (.of (awayOne K)) :=
  Spec.map (CommRingCat.ofHom (restrictOne K))

/-- Inclusion of the intersection into D(X). -/
def toLaurent : Spec (.of (puncture K)) ⟶ ProjectiveLine.overlap K :=
  Spec.map (CommRingCat.ofHom (torusRestriction K))

/-- The common inclusion of the puncture into the affine line. -/
def punctureOpen : Spec (.of (puncture K)) ⟶ ProjectiveLine.chart K :=
  Spec.map (CommRingCat.ofHom (algebraMap K[X] (puncture K)))

instance : IsOpenImmersion (punctureOpen K) :=
  IsOpenImmersion.of_isLocalization (X * (X - 1) : K[X])

@[reassoc (attr := simp)]
theorem toOne_openOne : toOne K ≫ openOne K = punctureOpen K := by
  rw [toOne, openOne, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (restrictOne_algebraMap K)

@[reassoc (attr := simp)]
theorem toLaurent_overlapLeft :
    toLaurent K ≫ ProjectiveLine.overlapLeft K = punctureOpen K := by
  rw [toLaurent, ProjectiveLine.overlapLeft, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    change torusRestriction K (Polynomial.toLaurent (C r)) =
      algebraMap K[X] (puncture K) (C r)
    rw [Polynomial.toLaurent_C, torusRestriction_C]
    exact IsScalarTower.algebraMap_apply K K[X] (puncture K) r
  · change torusRestriction K (Polynomial.toLaurent X) = algebraMap K[X] (puncture K) X
    simpa only [Polynomial.toLaurent_X, coordinate_val] using torusRestriction_T K

instance : IsOpenImmersion (toOne K) := by
  have : IsOpenImmersion (toOne K ≫ openOne K) := by rw [toOne_openOne]; infer_instance
  exact IsOpenImmersion.of_comp _ (openOne K)

/-- The two chosen maps to the affine line commute. -/
theorem condition : toLaurent K ≫ ProjectiveLine.overlapLeft K = toOne K ≫ openOne K := by
  rw [toLaurent_overlapLeft, toOne_openOne]

/-- The puncture really is the intersection of these two principal opens. -/
theorem isPullback :
    IsPullback (toLaurent K) (toOne K) (ProjectiveLine.overlapLeft K) (openOne K) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (condition K).symm
  apply TopologicalSpace.Opens.ext
  ext x
  change openOne K x ∈ Set.range (ProjectiveLine.overlapLeft K) ↔ x ∈ Set.range (toOne K)
  have hX : Set.range (ProjectiveLine.overlapLeft K) =
      (PrimeSpectrum.basicOpen (X : K[X]) : Set (PrimeSpectrum K[X])) :=
    PrimeSpectrum.localization_away_comap_range K[T;T⁻¹] X
  rw [hX]
  constructor
  · intro hx
    have hd : openOne K x ∈ (PrimeSpectrum.basicOpen (X - 1 : K[X]) :
        Set (PrimeSpectrum K[X])) := by
      rw [← PrimeSpectrum.localization_away_comap_range (awayOne K) (X - 1 : K[X])]
      exact ⟨x, rfl⟩
    have hp : openOne K x ∈ Set.range (punctureOpen K) := by
      rw [show Set.range (punctureOpen K) =
        (PrimeSpectrum.basicOpen (X * (X - 1) : K[X]) : Set (PrimeSpectrum K[X])) from
          PrimeSpectrum.localization_away_comap_range (puncture K) _]
      simpa only [PrimeSpectrum.basicOpen_mul, TopologicalSpace.Opens.coe_inf,
        Set.mem_inter_iff] using And.intro hx hd
    obtain ⟨y, hy⟩ := hp
    refine ⟨y, (openOne K).isOpenEmbedding.injective ?_⟩
    change (toOne K ≫ openOne K) y = openOne K x
    rwa [toOne_openOne]
  · rintro ⟨y, rfl⟩
    have hy : openOne K (toOne K y) = ProjectiveLine.overlapLeft K (toLaurent K y) :=
      congrArg (fun f ↦ f y) (condition K).symm
    rw [hy, ← hX]
    exact ⟨toLaurent K y, rfl⟩

/-- D(X) and D(X-1) cover, over fields of every characteristic. -/
theorem covers (x : ProjectiveLine.chart K) :
    x ∈ Set.range (ProjectiveLine.overlapLeft K) ∨ x ∈ Set.range (openOne K) := by
  rw [show Set.range (ProjectiveLine.overlapLeft K) =
    (PrimeSpectrum.basicOpen (X : K[X]) : Set (PrimeSpectrum K[X])) from
      PrimeSpectrum.localization_away_comap_range K[T;T⁻¹] X]
  rw [show Set.range (openOne K) =
    (PrimeSpectrum.basicOpen (X - 1 : K[X]) : Set (PrimeSpectrum K[X])) from
      PrimeSpectrum.localization_away_comap_range (awayOne K) _]
  change X ∉ x.asIdeal ∨ X - 1 ∉ x.asIdeal
  by_contra h
  have h' : X ∈ x.asIdeal ∧ X - 1 ∈ x.asIdeal := by
    simpa only [PrimeSpectrum.mem_basicOpen, not_or, not_not] using h
  have hone : (1 : K[X]) ∈ x.asIdeal := by
    simpa using x.asIdeal.sub_mem h'.1 h'.2
  exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem x.asIdeal hone isUnit_one)

/-- This cover admits descent to arbitrary schemes. -/
theorem isPushout :
    IsPushout (toLaurent K) (toOne K) (ProjectiveLine.overlapLeft K) (openOne K) :=
  BinaryOpenDescent.isPushout _ _ _ _ (isPullback K) (covers K)

end FLT.Mazur.OneGonAffineCover

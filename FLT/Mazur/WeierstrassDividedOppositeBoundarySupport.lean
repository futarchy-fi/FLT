/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedExteriorIntersection

/-!
# Opposite depth boundaries meet only away from the special fiber

The previous and next boundary opens are D(u) and D(t). Their intersection
is exactly D(π), by the original incidence relation t*u = π.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π k) (e : Data W π (k + 1))
open WeierstrassSuccessiveX
local notation "T" => Coordinate W (π ^ k) π (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ k) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "u" => coord W (π ^ k) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 2

omit [IsDomain R] in
/-- The next actual boundary has precisely the incidence principal-open image. -/
theorem nextToX_range_basicOpen :
    Set.range (nextToX e) = (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum T)) := by
  unfold nextToX
  change Set.range ((xOpenInclusion _ _ _ _ _ _) ∘
    ((overlapIso _ _ _ _ _ _).inv ∘ (nextBoundaryIso e).hom)) = _
  exact (((overlapIso _ _ _ _ _ _).inv.homeomorph.surjective.comp
    (nextBoundaryIso e).hom.homeomorph.surjective).range_comp _).trans
    (PrimeSpectrum.localization_away_comap_range _ t)

/-- The previous actual boundary has precisely the horizontal principal-open image. -/
theorem previousToX_range_basicOpen :
    Set.range (previousToX hπ d e) =
      (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum T)) := by
  unfold previousToX
  change Set.range ((horizontalOpenInclusion _ _ _ _ _ _) ∘
    ((horizontalIso _ _ _ _ _ _).inv ∘ (previousBoundaryIso hπ d e).inv)) = _
  exact (((horizontalIso _ _ _ _ _ _).inv.homeomorph.surjective.comp
    (previousBoundaryIso hπ d e).inv.homeomorph.surjective).range_comp _).trans
    (PrimeSpectrum.localization_away_comap_range _ u)

/-- The entire overlap of the two opposite boundaries lies exactly over D(π). -/
theorem oppositeBoundary_intersection :
    Set.range (nextToX e) ∩ Set.range (previousToX hπ d e) =
      (PrimeSpectrum.basicOpen (algebraMap R T π) : Set (PrimeSpectrum T)) := by
  rw [nextToX_range_basicOpen e, previousToX_range_basicOpen hπ d e]
  ext z
  change (t ∉ z.asIdeal ∧ u ∉ z.asIdeal) ↔ algebraMap R T π ∉ z.asIdeal
  rw [← incidence W (π ^ k) π e.b3 e.b4 e.b6, z.isPrime.mul_mem_iff_mem_or_mem]
  exact (not_or).symm

/-- A point meeting both original boundaries cannot lie above the special fiber. -/
theorem oppositeBoundary_parameter_notMem (z : stepX e)
    (hn : z ∈ Set.range (nextToX e)) (hp : z ∈ Set.range (previousToX hπ d e)) :
    π ∉ (Spec.map (CommRingCat.ofHom (algebraMap R T)) z).asIdeal := by
  have hz := Set.mem_inter hn hp
  rw [oppositeBoundary_intersection hπ d e] at hz
  exact hz

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberUnitScalingGeometry

/-!
# Full puncture ranges under unit normalization

Scaling the first coordinate by a base unit preserves its principal open.
Thus the entire original puncture becomes the corresponding polygon puncture.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.NodalFiber
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (c t : R) (u : Rˣ) (hc : c = t * ↑u)
local notation "e" => unitSmoothingIso c t u hc

/-- Inverse normalization pulls either full node puncture back to its polygon puncture. -/
theorem unitSmoothingIso_inv_preimage_puncture (opposite : Bool) :
    (e).inv ⁻¹' (PrimeSpectrum.basicOpen (if opposite then p c else q c) :
      Set (PrimeSpectrum (Coordinate c))) =
    (PrimeSpectrum.basicOpen (if opposite then PolygonSmoothing.leftCoordinate t
      else PolygonSmoothing.rightCoordinate t) : Set (PrimeSpectrum _)) := by
  ext x
  change (unitSmoothingEquiv c t u hc (if opposite then p c else q c) ∉ x.asIdeal) ↔ _
  cases opposite
  · simp only [Bool.false_eq_true, ↓reduceIte, unitSmoothingEquiv_q]
    rfl
  · simp only [↓reduceIte, unitSmoothingEquiv_p]
    exact not_congr (x.asIdeal.unit_mul_mem_iff_mem (u.isUnit.map (algebraMap R _)))

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of (Coordinate c)))

/-- The entire normalized boundary has exactly the standard polygon puncture as its range. -/
theorem unitSmoothingIso_comp_range (opposite : Bool)
    (hf : Set.range f = (PrimeSpectrum.basicOpen (if opposite then p c else q c) :
      Set (PrimeSpectrum (Coordinate c)))) :
    Set.range (f ≫ (e).hom) = Set.range
      (if opposite then PolygonSmoothing.leftBranchOpen R t
        else PolygonSmoothing.rightBranchOpen R t) := by
  change Set.range ((e).hom ∘ f) = _
  rw [Set.range_comp, hf]
  have he : (e).hom '' (PrimeSpectrum.basicOpen (if opposite then p c else q c) :
      Set (PrimeSpectrum (Coordinate c))) =
      (e).inv ⁻¹' (PrimeSpectrum.basicOpen (if opposite then p c else q c) :
        Set (PrimeSpectrum (Coordinate c))) :=
    (Scheme.homeoOfIso (e)).image_eq_preimage_symm _
  rw [he, unitSmoothingIso_inv_preimage_puncture]
  cases opposite
  · exact (PolygonSmoothing.rightBranchOpen_range R t).symm
  · exact (PolygonSmoothing.leftBranchOpen_range R t).symm

end FLT.Mazur.NodalFiber

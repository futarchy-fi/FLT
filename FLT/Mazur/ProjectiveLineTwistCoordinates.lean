/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveUnitChartPoint
public import FLT.Mazur.LineTrivializationCocycle

/-!
# Independence of coordinates on the test-base line twist

A family in a trivialized rank-one module defines a projective point wherever
one member is a unit in that trivialization. Changing the actual line
trivialization leaves the scheme morphism unchanged. Applied to structure
sheaf sections, this includes genuine test-base line bundles on common opens.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u v
namespace FLT.Mazur.ProjectiveSpace
open Approximation
variable (R : Type u) [CommRing R] (ι : Type u)
variable {S : Type u} [CommRing S] {L : Type v} [AddCommGroup L] [Module S L]

/-- Coordinates of a family valued in a test-base line define a projective scheme point. -/
def lineTwistPoint (f : R →+* S) (s : ι → L) (e : L ≃ₗ[S] S)
    (i : ι) (a : Sˣ) (hi : e (s i) = a) : Spec (.of S) ⟶ space R ι :=
  unitChartPoint R ι f (fun k ↦ e (s k)) i a hi

/-- A genuine change of line trivialization rescales all coordinates by its unit ratio. -/
lemma lineTwistPoint_trivialization (f : R →+* S) (s : ι → L) (e d : L ≃ₗ[S] S)
    (i : ι) (a : Sˣ) (hi : d (s i) = a) :
    lineTwistPoint R ι f s e i (linearCoordinateRatio e d * a)
        (by rw [linearCoordinateRatio_smul e d, hi]; rfl) =
      lineTwistPoint R ι f s d i a hi := by
  have he : (fun k ↦ e (s k)) = fun k ↦ (linearCoordinateRatio e d : S) * d (s k) := by
    funext k
    exact linearCoordinateRatio_smul e d (s k)
  unfold lineTwistPoint
  simpa only [← he] using
    unitChartPoint_scale R ι f (fun k ↦ d (s k)) i a (linearCoordinateRatio e d) hi

/-- Both the unit coordinate and the line trivialization may be changed simultaneously. -/
lemma lineTwistPoint_change (f : R →+* S) (s : ι → L) (e d : L ≃ₗ[S] S)
    (i j : ι) (a b : Sˣ) (hi : e (s i) = a) (hj : d (s j) = b) :
    lineTwistPoint R ι f s e i a hi = lineTwistPoint R ι f s d j b hj := by
  trans lineTwistPoint R ι f s e j (linearCoordinateRatio e d * b)
    (by rw [linearCoordinateRatio_smul e d, hj]; rfl)
  · exact unitChartPoint_change R ι f _ i j a _ hi
      (by rw [linearCoordinateRatio_smul e d, hj]; rfl)
  · exact lineTwistPoint_trivialization R ι f s e d j b hj

variable {X : Scheme.{u}} {M : X.Modules} {U V W : X.Opens}

/-- Actual local trivializations of a sheaf line twist give identical chart morphisms. -/
lemma lineTwistPoint_sheaf_trivialization
    (e : M.restrict U.ι ≅ FCurve.structureModule U.toScheme)
    (d : M.restrict V.ι ≅ FCurve.structureModule V.toScheme)
    (hU : W ≤ U) (hV : W ≤ V) (f : R →+* Γ(X, W))
    (s : ι → Γ(M, W)) (i j : ι) (a b : Γ(X, W)ˣ)
    (hi : FCurve.lineTrivializationCoordinates e hU (s i) = a)
    (hj : FCurve.lineTrivializationCoordinates d hV (s j) = b) :
    lineTwistPoint R ι f s (FCurve.lineTrivializationCoordinates e hU) i a hi =
      lineTwistPoint R ι f s (FCurve.lineTrivializationCoordinates d hV) j b hj :=
  lineTwistPoint_change R ι f s _ _ i j a b hi hj

end FLT.Mazur.ProjectiveSpace

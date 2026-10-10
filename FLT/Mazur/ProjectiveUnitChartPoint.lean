/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveUnitChartEvaluation
public import FLT.Mazur.ProjectiveChartMapCompatibilityUniverse
public import FLT.Mazur.ProjectiveChartPointMembership

/-!
# Scheme points from tuples with a unit coordinate

The actual map into Proj does not depend on the selected unit coordinate or
on unit rescaling. Its chart membership is detected by the original tuple.
These statements supply the local scheme maps needed for line-bundle descent.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) [CommRing R] (ι : Type u)
variable {S : Type u} [CommRing S]

/-- A unit coordinate gives an actual morphism into projective space. -/
def unitChartPoint (f : R →+* S) (x : ι → S) (i : ι) (a : Sˣ) (hi : x i = a) :
    Spec (.of S) ⟶ space R ι :=
  Spec.map (CommRingCat.ofHom (unitChartEval R ι f x i a hi)) ≫ chartMap R ι i

/-- Changing the chosen unit coordinate leaves the scheme point unchanged. -/
lemma unitChartPoint_change (f : R →+* S) (x : ι → S) (i j : ι)
    (a b : Sˣ) (hi : x i = a) (hj : x j = b) :
    unitChartPoint R ι f x i a hi = unitChartPoint R ι f x j b hj := by
  apply chartMaps_eq_of_coordinates_universe R S ι i j
  · intro r
    simp only [unitChartEval_scalar]
  · intro k
    simp only [unitChartEval_coordinate, hj]
    calc
      (↑a⁻¹ : S) * x k = (↑a⁻¹ : S) * x k * ((↑b⁻¹ : S) * b) := by simp
      _ = (↑b⁻¹ : S) * x k * ((↑a⁻¹ : S) * b) := by ring
  · simp only [unitChartEval_coordinate, hj]
    exact a⁻¹.isUnit.mul b.isUnit

/-- Unit rescaling changes only the trivialization of the represented line. -/
lemma unitChartPoint_scale (f : R →+* S) (x : ι → S) (i : ι) (a b : Sˣ)
    (hi : x i = a) :
    unitChartPoint R ι f (fun j ↦ (b : S) * x j) i (b * a) (by simp [hi]) =
      unitChartPoint R ι f x i a hi := by
  unfold unitChartPoint
  rw [unitChartEval_scale]

/-- The constructed point has exactly the prescribed coefficient map. -/
@[reassoc]
lemma unitChartPoint_baseProjection (f : R →+* S) (x : ι → S) (i : ι)
    (a : Sˣ) (hi : x i = a) :
    unitChartPoint R ι f x i a hi ≫ baseProjection R ι = Spec.map (CommRingCat.ofHom f) := by
  rw [unitChartPoint, Category.assoc, chartMap_baseProjection, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (unitChartEval_scalar R ι f x i a hi)

/-- The projective point commutes with arbitrary maps of affine test schemes. -/
@[reassoc]
lemma unitChartPoint_map {T : Type u} [CommRing T] (g : S →+* T)
    (f : R →+* S) (x : ι → S) (i : ι) (a : Sˣ) (hi : x i = a) :
    Spec.map (CommRingCat.ofHom g) ≫ unitChartPoint R ι f x i a hi =
      unitChartPoint R ι (g.comp f) (fun j ↦ g (x j)) i
        (Units.map g a) (by simp [hi]) := by
  simp only [unitChartPoint, ← Category.assoc, ← Spec.map_comp]
  congr 1
  exact congrArg (fun h ↦ Spec.map (CommRingCat.ofHom h))
    (unitChartEval_map R ι g f x i a hi)

/-- The image lies in another projective chart precisely where that coordinate is nonzero. -/
lemma unitChartPoint_mem_chart (f : R →+* S) (x : ι → S) (i j : ι)
    (a : Sˣ) (hi : x i = a) (p : Spec (.of S)) :
    unitChartPoint R ι f x i a hi p ∈ chart R ι j ↔ x j ∉ p.asIdeal := by
  rw [unitChartPoint, spec_chartMap_mem_iff, unitChartEval_coordinate]
  constructor
  · intro h hx
    exact h (p.asIdeal.mul_mem_left _ hx)
  · intro h hx
    apply h
    have hmul := p.asIdeal.mul_mem_left (a : S) hx
    simpa only [← mul_assoc, Units.mul_inv, one_mul] using hmul

end FLT.Mazur.ProjectiveSpace

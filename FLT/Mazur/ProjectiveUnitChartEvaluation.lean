/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SegreChartMaps

/-!
# Projective chart evaluation at a unit coordinate

Normalize a tuple by its chosen unit coordinate. This works over arbitrary
rings and for arbitrary coordinate index types. The chart functor is exactly
the functor of normalized tuples, and changing a trivialization by a unit
does not change its chart evaluation.
-/

@[expose] public noncomputable section
open MvPolynomial HomogeneousLocalization
universe u v w
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) [CommRing R] (ι : Type v)
variable {S : Type w} [CommRing S]

/-- Chart maps over a fixed coefficient map classify normalized tuples. -/
def normalizedChartEquiv (f : R →+* S) (i : ι) :
    {x : ι → S // x i = 1} ≃
      {g : chartRing R ι i →+* S // ∀ r, g (chartScalars R ι i r) = f r} where
  toFun x := ⟨chartEval R ι f x.val i x.property, chartEval_scalar R ι f x.val i x.property⟩
  invFun g := ⟨fun j ↦ g.val (coordinate R ι i j), by simp⟩
  left_inv x := by
    apply Subtype.ext
    funext j
    exact chartEval_coordinate R ι f x.val i x.property j
  right_inv g := by
    apply Subtype.ext
    apply chartRing_hom_ext R ι i
    · intro r
      simpa only [chartEval_scalar] using (g.property r).symm
    · intro j
      simp only [chartEval_coordinate]

/-- Evaluate in a chart by dividing all coordinates by the selected unit. -/
def unitChartEval (f : R →+* S) (x : ι → S) (i : ι) (a : Sˣ)
    (hi : x i = a) : chartRing R ι i →+* S :=
  chartEval R ι f (fun j ↦ (↑a⁻¹ : S) * x j) i (by simp [hi])

/-- Scalars retain the specified coefficient homomorphism. -/
@[simp]
lemma unitChartEval_scalar (f : R →+* S) (x : ι → S) (i : ι) (a : Sˣ)
    (hi : x i = a) (r : R) :
    unitChartEval R ι f x i a hi (chartScalars R ι i r) = f r :=
  chartEval_scalar R ι f _ i _ r

/-- The affine coordinate is the ratio to the chosen homogeneous coordinate. -/
@[simp]
lemma unitChartEval_coordinate (f : R →+* S) (x : ι → S) (i : ι) (a : Sˣ)
    (hi : x i = a) (j : ι) :
    unitChartEval R ι f x i a hi (coordinate R ι i j) = (↑a⁻¹ : S) * x j :=
  chartEval_coordinate R ι f _ i _ j

/-- A homogeneous fraction evaluates as numerator divided by the denominator power. -/
lemma unitChartEval_mk (f : R →+* S) (x : ι → S) (i : ι) (a : Sˣ)
    (hi : x i = a) (d : ℕ) (p : MvPolynomial ι R)
    (hp : p ∈ grading R ι (d • 1)) :
    unitChartEval R ι f x i a hi (Away.mk _ (isHomogeneous_X R i) d p hp) =
      (↑a⁻¹ : S) ^ d * eval₂ f x p := by
  rw [unitChartEval, chartEval_mk]
  exact homogeneous_eval₂_scale R f x _ (by simpa using hp)

/-- Changing a line trivialization by a unit preserves its chart map. -/
lemma unitChartEval_scale (f : R →+* S) (x : ι → S) (i : ι) (a b : Sˣ)
    (hi : x i = a) :
    unitChartEval R ι f (fun j ↦ (b : S) * x j) i (b * a) (by simp [hi]) =
      unitChartEval R ι f x i a hi := by
  apply chartRing_hom_ext R ι i
  · intro r
    simp only [unitChartEval_scalar]
  · intro j
    simp [mul_assoc]

/-- Evaluation commutes with arbitrary coefficient homomorphisms of test rings. -/
lemma unitChartEval_map {T : Type*} [CommRing T] (g : S →+* T)
    (f : R →+* S) (x : ι → S) (i : ι) (a : Sˣ) (hi : x i = a) :
    g.comp (unitChartEval R ι f x i a hi) =
      unitChartEval R ι (g.comp f) (fun j ↦ g (x j)) i
        (Units.map g a) (by simp [hi]) := by
  apply chartRing_hom_ext R ι i
  · intro r
    simp only [RingHom.comp_apply, unitChartEval_scalar]
  · intro j
    simp only [RingHom.comp_apply, unitChartEval_coordinate, map_mul]
    rfl

end FLT.Mazur.ProjectiveSpace

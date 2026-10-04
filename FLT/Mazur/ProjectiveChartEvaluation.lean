/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveChartPolynomialEquiv
public import FLT.Mazur.ProjectiveSpaceReindex

/-!
# Evaluation of arbitrary finite projective chart rings

The existing zeroth-chart polynomial equivalence, followed by homogeneous
coordinate reindexing, evaluates every chart at a normalized coordinate family.
The denominator coordinate must equal one; no gluing is assumed.
-/

open CategoryTheory AlgebraicGeometry MvPolynomial
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R S : Type u) [CommRing R] [CommRing S] (n : ℕ)

/-- Evaluate the zeroth projective chart through its polynomial equivalence. -/
def zeroChartEvaluation (r : R →+* S) (v : Fin (n + 1) → S) :
    chartRing R (Fin (n + 1)) 0 →+* S :=
  (eval₂Hom r (fun i ↦ v i.succ)).comp (chartPolynomialEquiv R n).symm.toRingHom

/-- The scalar map is the chosen coefficient homomorphism. -/
@[simp] lemma zeroChartEvaluation_scalar (r : R →+* S) (v : Fin (n + 1) → S) (a : R) :
    zeroChartEvaluation R S n r v (chartScalars R (Fin (n + 1)) 0 a) = r a := by
  change eval₂Hom r _ (chartToPolynomial R n (chartScalars R _ 0 a)) = _
  rw [chartToPolynomial_scalar, eval₂Hom_C]

/-- All homogeneous coordinate ratios evaluate at their prescribed values. -/
lemma zeroChartEvaluation_coordinate (r : R →+* S) (v : Fin (n + 1) → S)
    (hv : v 0 = 1) (j : Fin (n + 1)) :
    zeroChartEvaluation R S n r v (coordinate R (Fin (n + 1)) 0 j) = v j := by
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · rw [coordinate_self, map_one, hv]
  · change eval₂Hom r _ (chartToPolynomial R n (coordinate R _ 0 i.succ)) = _
    rw [chartToPolynomial_coordinate, eval₂Hom_X']

variable {ι : Type}

/-- Move the chosen denominator to the zeroth coordinate in the chart ring. -/
def chartReindexZero (e : Fin (n + 1) ≃ ι) (i : ι) (hi : e.symm i = 0) :
    chartRing R ι i →+* chartRing R (Fin (n + 1)) 0 :=
  HomogeneousLocalization.map (renameGraded R e.symm) (by
    rintro _ ⟨k, rfl⟩
    exact ⟨k, by simp [hi]⟩)

/-- Reindexing to zero carries every coordinate to the corresponding normalized coordinate. -/
lemma chartReindexZero_coordinate (e : Fin (n + 1) ≃ ι) (i : ι)
    (hi : e.symm i = 0) (j : ι) :
    chartReindexZero R n e i hi (coordinate R ι i j) =
      coordinate R (Fin (n + 1)) 0 (e.symm j) := by
  apply HomogeneousLocalization.val_injective
  simp [chartReindexZero, coordinate, HomogeneousLocalization.Away.mk,
    HomogeneousLocalization.map_mk, hi]

/-- Reindexing retains the scalar coefficient map. -/
lemma chartReindexZero_scalar (e : Fin (n + 1) ≃ ι) (i : ι)
    (hi : e.symm i = 0) (a : R) :
    chartReindexZero R n e i hi (chartScalars R ι i a) =
      chartScalars R (Fin (n + 1)) 0 a := by
  apply HomogeneousLocalization.val_injective
  simp [chartReindexZero, chartScalars, constantsToZero,
    HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.map_mk]

/-- Evaluate any finite projective chart after reindexing its denominator to zero. -/
def chartEvaluation (e : Fin (n + 1) ≃ ι) (i : ι) (hi : e.symm i = 0)
    (r : R →+* S) (v : ι → S) : chartRing R ι i →+* S :=
  (zeroChartEvaluation R S n r (v ∘ e)).comp (chartReindexZero R n e i hi)

/-- Chart evaluation extends the chosen scalar homomorphism. -/
lemma chartEvaluation_scalar (e : Fin (n + 1) ≃ ι) (i : ι)
    (hi : e.symm i = 0) (r : R →+* S) (v : ι → S) (a : R) :
    chartEvaluation R S n e i hi r v (chartScalars R ι i a) = r a := by
  rw [chartEvaluation, RingHom.comp_apply, chartReindexZero_scalar,
    zeroChartEvaluation_scalar]

/-- The arbitrary chart evaluation sends each ratio to the prescribed normalized coordinate. -/
lemma chartEvaluation_coordinate (e : Fin (n + 1) ≃ ι) (i : ι)
    (hi : e.symm i = 0) (r : R →+* S) (v : ι → S) (hv : v i = 1) (j : ι) :
    chartEvaluation R S n e i hi r v (coordinate R ι i j) = v j := by
  have hv0 : (v ∘ e) 0 = 1 := by rw [Function.comp_apply, ← hi]; simpa using hv
  rw [chartEvaluation, RingHom.comp_apply, chartReindexZero_coordinate,
    zeroChartEvaluation_coordinate R S n r (v ∘ e) hv0]
  simp

end FLT.Mazur.ProjectiveSpace

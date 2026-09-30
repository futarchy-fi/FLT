/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveChartPolynomialEquiv
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Coordinate maps for the Segre construction

On a pair of standard projective charts the matrix coordinates are products
of the two normalized coordinate vectors.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open scoped TensorProduct

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι κ : Type u)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Evaluate homogeneous fractions at a coordinate vector normalized at `i`. -/
def chartEval {S : Type u} [CommRing S] (f : R →+* S) (x : ι → S)
    (i : ι) (hi : x i = 1) : chartRing R ι i →+* S :=
  (Localization.awayLift (eval₂Hom f x) (X i) (by simp [hi])).comp
    (algebraMap _ (Localization.Away (X (R := R) i)))

lemma chartEval_mk {S : Type u} [CommRing S] (f : R →+* S) (x : ι → S)
    (i : ι) (hi : x i = 1) (d : ℕ) (p : MvPolynomial ι R)
    (hp : p ∈ grading R ι (d • 1)) :
    chartEval R ι f x i hi (Away.mk _ (isHomogeneous_X R i) d p hp) =
      eval₂ f x p := by
  change Localization.awayLift (eval₂Hom f x) (X i) (by simp [hi])
    (Localization.mk p _) = _
  simpa using Localization.awayLift_mk (eval₂Hom f x) (X i) p 1 (by simp [hi]) d

@[simp]
lemma chartEval_coordinate {S : Type u} [CommRing S] (f : R →+* S) (x : ι → S)
    (i : ι) (hi : x i = 1) (j : ι) :
    chartEval R ι f x i hi (coordinate R ι i j) = x j := by
  rw [coordinate, chartEval_mk, eval₂_X]

@[simp]
lemma chartEval_scalar {S : Type u} [CommRing S] (f : R →+* S) (x : ι → S)
    (i : ι) (hi : x i = 1) (r : R) :
    chartEval R ι f x i hi (chartScalars R ι i r) = f r := by
  change chartEval R ι f x i hi (Away.mk _ (isHomogeneous_X R i) 0 (C r) _) = _
  rw [chartEval_mk, eval₂_C]

/-- A homogeneous fraction is its numerator evaluated at the chart coordinates. -/
lemma eval₂_coordinate_mk (i : ι) (d : ℕ) (p : MvPolynomial ι R)
    (hp : p ∈ grading R ι (d • 1)) :
    eval₂ (chartScalars R ι i) (coordinate R ι i) p =
      Away.mk _ (isHomogeneous_X R i) d p hp := by
  apply val_injective
  let v := algebraMap (chartRing R ι i) (Localization.Away (X (R := R) i))
  change v (eval₂ _ _ p) = _
  rw [hom_eval₂]
  have hv : v.comp (chartScalars R ι i) =
      (algebraMap (MvPolynomial ι R) (Localization.Away (X (R := R) i))).comp C := by
    ext r
    exact val_chartScalars R ι i r
  rw [hv]
  have hc (j : ι) : v (coordinate R ι i j) =
      Localization.mk 1 ⟨X i, Submonoid.mem_powers _⟩ *
        algebraMap (MvPolynomial ι R) (Localization.Away (X (R := R) i)) (X j) := by
    simp only [v, HomogeneousLocalization.algebraMap_apply, coordinate, Away.val_mk, pow_one,
      ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul, mul_one]
  simp_rw [hc]
  rw [homogeneous_eval₂_scale R _ _ _ (by simpa using hp)]
  rw [← hom_eval₂, eval₂_eta]
  simp only [Localization.mk_pow, one_pow, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul, one_mul, mul_one, Away.val_mk]
  rfl

/-- Ring maps out of a standard chart are determined by scalars and coordinates. -/
lemma chartRing_hom_ext {S : Type u} [CommRing S] (i : ι)
    (f g : chartRing R ι i →+* S)
    (hR : ∀ r, f (chartScalars R ι i r) = g (chartScalars R ι i r))
    (hX : ∀ j, f (coordinate R ι i j) = g (coordinate R ι i j)) : f = g := by
  ext z
  obtain ⟨d, p, hp, rfl⟩ := Away.mk_surjective (grading R ι) (isHomogeneous_X R i) z
  rw [← eval₂_coordinate_mk, hom_eval₂, hom_eval₂]
  congr 1
  · exact RingHom.ext hR
  · exact funext hX

/-- The coordinate ring of a pair of standard affine charts. -/
abbrev segreSourceRing (i : ι) (j : κ) := chartRing R ι i ⊗[R] chartRing R κ j

/-- The rank-one matrix on a pair of affine charts. -/
def segreCoordinate (i : ι) (j : κ) (p : ι × κ) : segreSourceRing R ι κ i j :=
  coordinate R ι i p.1 ⊗ₜ[R] coordinate R κ j p.2

@[simp]
lemma segreCoordinate_self (i : ι) (j : κ) :
    segreCoordinate R ι κ i j (i, j) = 1 := by
  simp [segreCoordinate, Algebra.TensorProduct.one_def]

/-- The pullback on coordinate rings for one affine Segre chart. -/
def segreChartMap (i : ι) (j : κ) :
    chartRing R (ι × κ) (i, j) →ₐ[R] segreSourceRing R ι κ i j :=
  { chartEval R (ι × κ) (algebraMap R _) (segreCoordinate R ι κ i j)
      (i, j) (segreCoordinate_self R ι κ i j) with
    commutes' := chartEval_scalar R (ι × κ) _ _ _ _ }

@[simp]
lemma segreChartMap_coordinate (i : ι) (j : κ) (p : ι × κ) :
    segreChartMap R ι κ i j (coordinate R (ι × κ) (i, j) p) =
      segreCoordinate R ι κ i j p :=
  chartEval_coordinate R (ι × κ) _ _ _ (segreCoordinate_self R ι κ i j) p

/-- Every two-by-two minor vanishes on the affine Segre chart. -/
lemma segreCoordinate_minor (i a b : ι) (j c d : κ) :
    segreCoordinate R ι κ i j (a, c) * segreCoordinate R ι κ i j (b, d) -
      segreCoordinate R ι κ i j (a, d) * segreCoordinate R ι κ i j (b, c) = 0 := by
  simp only [segreCoordinate, Algebra.TensorProduct.tmul_mul_tmul, mul_comm
    (coordinate R κ j c) (coordinate R κ j d), sub_self]

/-- The affine Segre map is surjective on coordinate rings. -/
lemma segreChartMap_surjective (i : ι) (j : κ) :
    Function.Surjective (segreChartMap R ι κ i j) := by
  have hleft (x : chartRing R ι i) :
      x ⊗ₜ[R] (1 : chartRing R κ j) ∈ (segreChartMap R ι κ i j).range := by
    obtain ⟨d, p, hp, rfl⟩ := Away.mk_surjective (grading R ι) (isHomogeneous_X R i) x
    rw [← eval₂_coordinate_mk]
    change (Algebra.TensorProduct.includeLeft : chartRing R ι i →ₐ[R] _)
      ((aeval (coordinate R ι i)) p) ∈ _
    rw [← AlgHom.comp_apply]
    have h : ((Algebra.TensorProduct.includeLeft : chartRing R ι i →ₐ[R] _).comp
        (aeval (coordinate R ι i))) = (segreChartMap R ι κ i j).comp
          (aeval (fun a ↦ coordinate R (ι × κ) (i, j) (a, j))) := by
      ext a
      simp [segreCoordinate]
    rw [h]
    exact ⟨_, rfl⟩
  have hright (y : chartRing R κ j) :
      (1 : chartRing R ι i) ⊗ₜ[R] y ∈ (segreChartMap R ι κ i j).range := by
    obtain ⟨d, p, hp, rfl⟩ := Away.mk_surjective (grading R κ) (isHomogeneous_X R j) y
    rw [← eval₂_coordinate_mk]
    change (Algebra.TensorProduct.includeRight : chartRing R κ j →ₐ[R] _)
      ((aeval (coordinate R κ j)) p) ∈ _
    rw [← AlgHom.comp_apply]
    have h : ((Algebra.TensorProduct.includeRight : chartRing R κ j →ₐ[R] _).comp
        (aeval (coordinate R κ j))) = (segreChartMap R ι κ i j).comp
          (aeval (fun b ↦ coordinate R (ι × κ) (i, j) (i, b))) := by
      ext b
      simp [segreCoordinate]
    rw [h]
    exact ⟨_, rfl⟩
  intro z
  change z ∈ (segreChartMap R ι κ i j).range
  refine TensorProduct.inductionOn z ?_ ?_
  · intro x y
    simpa only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] using
      mul_mem (hleft x) (hright y)
  · intro x y hx hy
    exact add_mem hx hy

/-- Scalars on a standard overlap. -/
instance overlapAlgebra (i k : ι) : Algebra R (overlapRing R ι i k) :=
  ((fromZeroRingHom (grading R ι) _).comp (constantsToZero R ι)).toAlgebra

/-- Restriction from the first chart to an overlap, as an algebra map. -/
def chartOverlapLeft (i k : ι) : chartRing R ι i →ₐ[R] overlapRing R ι i k :=
  { toOverlap R ι i k with
    commutes' := fun r ↦ awayMap_fromZeroRingHom _ _ _ (constantsToZero R ι r) }

/-- Restriction from the second chart to the same overlap. -/
def chartOverlapRight (i k : ι) : chartRing R ι k →ₐ[R] overlapRing R ι i k :=
  { awayMap (grading R ι) (isHomogeneous_X R i) (mul_comm (X i) (X k)) with
    commutes' := fun r ↦ awayMap_fromZeroRingHom _ _ _ (constantsToZero R ι r) }

/-- Coordinate change between two standard projective charts. -/
lemma chartOverlap_coordinate (i k a : ι) :
    chartOverlapLeft R ι i k (coordinate R ι i a) =
      chartOverlapRight R ι i k (coordinate R ι k a) *
        chartOverlapLeft R ι i k (coordinate R ι i k) := by
  simp only [chartOverlapLeft, chartOverlapRight, AlgHom.coe_mk,
    toOverlap, coordinate, awayMap_mk]
  apply val_injective
  simp only [val_mul, Away.val_mk, pow_one, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

/-- Coordinate ring of the intersection of two pairs of standard charts. -/
abbrev segreOverlapRing (i k : ι) (j l : κ) :=
  overlapRing R ι i k ⊗[R] overlapRing R κ j l

/-- Restrict the first pair of charts to a product overlap. -/
def segreOverlapLeft (i k : ι) (j l : κ) :
    segreSourceRing R ι κ i j →ₐ[R] segreOverlapRing R ι κ i k j l :=
  Algebra.TensorProduct.map (chartOverlapLeft R ι i k) (chartOverlapLeft R κ j l)

/-- Restrict the second pair of charts to the same product overlap. -/
def segreOverlapRight (i k : ι) (j l : κ) :
    segreSourceRing R ι κ k l →ₐ[R] segreOverlapRing R ι κ i k j l :=
  Algebra.TensorProduct.map (chartOverlapRight R ι i k) (chartOverlapRight R κ j l)

/-- The Segre coordinates obey the target project's coordinate-change rule. -/
lemma segreOverlap_coordinate (i k : ι) (j l : κ) (p : ι × κ) :
    segreOverlapLeft R ι κ i k j l (segreCoordinate R ι κ i j p) =
      segreOverlapRight R ι κ i k j l (segreCoordinate R ι κ k l p) *
        segreOverlapLeft R ι κ i k j l (segreCoordinate R ι κ i j (k, l)) := by
  simp only [segreOverlapLeft, segreOverlapRight, segreCoordinate,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  rw [← chartOverlap_coordinate, ← chartOverlap_coordinate]

/-- The target chart-changing coordinate is invertible on the product overlap. -/
lemma segreOverlap_isUnit (i k : ι) (j l : κ) :
    IsUnit (segreOverlapLeft R ι κ i k j l (segreCoordinate R ι κ i j (k, l))) := by
  change IsUnit (toOverlap R ι i k (coordinate R ι i k) ⊗ₜ[R]
    toOverlap R κ j l (coordinate R κ j l))
  rw [← mul_one (toOverlap R ι i k (coordinate R ι i k)),
    ← one_mul (toOverlap R κ j l (coordinate R κ j l)),
    ← Algebra.TensorProduct.tmul_mul_tmul]
  exact ((isUnit_ratio R ι i k).map
    (Algebra.TensorProduct.includeLeft : overlapRing R ι i k →ₐ[R] _)).mul
      ((isUnit_ratio R κ j l).map
        (Algebra.TensorProduct.includeRight : overlapRing R κ j l →ₐ[R] _))

/-- Pullback from a target chart overlap to the product of source overlaps. -/
def segreOverlapMap (i k : ι) (j l : κ) :
    overlapRing R (ι × κ) (i, j) (k, l) →+* segreOverlapRing R ι κ i k j l := by
  letI := (toOverlap R (ι × κ) (i, j) (k, l)).toAlgebra
  letI := overlap_isLocalization R (ι × κ) (i, j) (k, l)
  exact IsLocalization.Away.lift (coordinate R (ι × κ) (i, j) (k, l))
    (g := ((segreOverlapLeft R ι κ i k j l).comp (segreChartMap R ι κ i j)).toRingHom)
    (by simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply,
      segreChartMap_coordinate] using segreOverlap_isUnit R ι κ i k j l)

/-- The first chart map restricts to the constructed overlap map. -/
lemma segreOverlapMap_left (i k : ι) (j l : κ) :
    (segreOverlapMap R ι κ i k j l).comp (chartOverlapLeft R (ι × κ) (i, j) (k, l)) =
      ((segreOverlapLeft R ι κ i k j l).comp (segreChartMap R ι κ i j)).toRingHom := by
  let := (toOverlap R (ι × κ) (i, j) (k, l)).toAlgebra
  let := overlap_isLocalization R (ι × κ) (i, j) (k, l)
  exact IsLocalization.Away.lift_comp _ _

/-- The second chart map has the same restriction on the overlap. -/
lemma segreOverlapMap_right (i k : ι) (j l : κ) :
    (segreOverlapMap R ι κ i k j l).comp (chartOverlapRight R (ι × κ) (i, j) (k, l)) =
      ((segreOverlapRight R ι κ i k j l).comp (segreChartMap R ι κ k l)).toRingHom := by
  have hleft (z : chartRing R (ι × κ) (i, j)) :=
    DFunLike.congr_fun (segreOverlapMap_left R ι κ i k j l) z
  apply chartRing_hom_ext
  · intro r
    change segreOverlapMap R ι κ i k j l
      (chartOverlapRight R (ι × κ) (i, j) (k, l) (algebraMap R _ r)) =
        segreOverlapRight R ι κ i k j l
          (segreChartMap R ι κ k l (algebraMap R _ r))
    rw [AlgHom.commutes]
    have h := hleft (algebraMap R _ r)
    simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.comp_apply, AlgHom.commutes] using h
  · intro p
    have h := congrArg (segreOverlapMap R ι κ i k j l)
      (chartOverlap_coordinate R (ι × κ) (i, j) (k, l) p)
    rw [map_mul] at h
    have hp := hleft (coordinate R (ι × κ) (i, j) p)
    have hkl := hleft (coordinate R (ι × κ) (i, j) (k, l))
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.comp_apply, segreChartMap_coordinate] at hp hkl ⊢
    rw [hp, hkl, segreOverlap_coordinate] at h
    exact (segreOverlap_isUnit R ι κ i k j l).mul_right_cancel h.symm

end FLT.Mazur.ProjectiveSpace

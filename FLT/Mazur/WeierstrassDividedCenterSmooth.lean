/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCenterTangent
public import FLT.Mazur.WeierstrassSuccessiveXReesChart

/-!
# Successive centers miss the divided chart's own smooth locus

The obstruction uses relative smoothness of the divided equation itself,
including exceptional smooth points above the original singular cubic.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
open PolygonNodePresentation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
local notation "A" => Coordinate W s b3 b4 b6

/-- A divided point with zero linear coefficients and zero coordinates is not smooth. -/
theorem dividedCenter_not_smooth (p : PrimeSpectrum A)
    (h3 : algebraMap R A b3 ∈ p.asIdeal) (h4 : algebraMap R A b4 ∈ p.asIdeal)
    (h6 : algebraMap R A b6 ∈ p.asIdeal)
    (hx : x W s b3 b4 b6 ∈ p.asIdeal) (hy : y W s b3 b4 b6 ∈ p.asIdeal) :
    p ∉ (Spec.map (CommRingCat.ofHom (algebraMap R A))).smoothLocus := by
  intro hp
  let K := p.asIdeal.ResidueField
  let e : A →ₐ[R] K := IsScalarTower.toAlgHom R A K
  have h3' : algebraMap R K b3 = 0 := by
    rw [IsScalarTower.algebraMap_apply R A K]
    exact Ideal.algebraMap_residueField_eq_zero.mpr h3
  have h4' : algebraMap R K b4 = 0 := by
    rw [IsScalarTower.algebraMap_apply R A K]
    exact Ideal.algebraMap_residueField_eq_zero.mpr h4
  have h6' : algebraMap R K b6 = 0 := by
    rw [IsScalarTower.algebraMap_apply R A K]
    exact Ideal.algebraMap_residueField_eq_zero.mpr h6
  apply relativeJet_origin_not_formallySmooth p.asIdeal e
    (dividedCenterTangent W s b3 b4 b6 h3' h6')
    (Ideal.ker_algebraMap_residueField p.asIdeal) ?_
    (dividedCenterTangent_no_lift W s b3 b4 b6 h3' h4' h6')
    (spec_smooth_implies_algebra p hp)
  apply hom_ext
  · simpa [AlgHom.comp_apply, e] using
      (Ideal.algebraMap_residueField_eq_zero.mpr hx).symm
  · simpa [AlgHom.comp_apply, e] using
      (Ideal.algebraMap_residueField_eq_zero.mpr hy).symm

variable (π : R)
local notation "B" => Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)

/-- The actual successive center is disjoint from the full relative divided smooth locus. -/
theorem successiveCenter_not_le_of_smooth (p : PrimeSpectrum B)
    (hp : p ∈ (Spec.map (CommRingCat.ofHom (algebraMap R B))).smoothLocus) :
    ¬ WeierstrassSuccessiveX.modificationCenter W s π b3 b4 b6 ≤ p.asIdeal := by
  intro hc
  have hπ : algebraMap R B π ∈ p.asIdeal := hc (Ideal.subset_span (by simp))
  apply dividedCenter_not_smooth W s (π * b3) (π * b4) (π ^ 2 * b6) p
    _ _ _ (hc (Ideal.subset_span (by simp))) (hc (Ideal.subset_span (by simp))) hp
  · rw [map_mul]
    exact p.asIdeal.mul_mem_right _ hπ
  · rw [map_mul]
    exact p.asIdeal.mul_mem_right _ hπ
  · rw [map_mul, map_pow]
    exact p.asIdeal.mul_mem_right _ (p.asIdeal.pow_mem_of_mem hπ 2 (by omega))

end FLT.Mazur.WeierstrassDilatation

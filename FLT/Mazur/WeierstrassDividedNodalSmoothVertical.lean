/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCenterSmooth

/-!
# Relative smoothness forces the vertical derivative on the strict nodal fiber

When the scale and the four lower coefficients vanish at the prime and the
mixed coefficient is a unit, a zero vertical derivative forces both coordinates
to vanish. The relative tangent obstruction then excludes smoothness.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
local notation "A" => Coordinate W s b3 b4 b6
local notation "x₀" => x W s b3 b4 b6
local notation "y₀" => y W s b3 b4 b6

/-- Every relatively smooth strict nodal point has nonvanishing vertical derivative. -/
theorem dividedNodal_smooth_vertical (p : PrimeSpectrum A) (ha : IsUnit W.a₁)
    (hs : algebraMap R A s ∈ p.asIdeal) (h2 : algebraMap R A W.a₂ ∈ p.asIdeal)
    (h3 : algebraMap R A b3 ∈ p.asIdeal) (h4 : algebraMap R A b4 ∈ p.asIdeal)
    (h6 : algebraMap R A b6 ∈ p.asIdeal)
    (hp : p ∈ (Spec.map (CommRingCat.ofHom (algebraMap R A))).smoothLocus) :
    verticalDerivative W s b3 b4 b6 ∉ p.asIdeal := by
  intro hd
  let K := p.asIdeal.ResidueField
  let e : A →ₐ[R] K := IsScalarTower.toAlgHom R A K
  have hz (r : R) (hr : algebraMap R A r ∈ p.asIdeal) : algebraMap R K r = 0 := by
    rw [IsScalarTower.algebraMap_apply R A K]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hr
  have hder : 2 * e y₀ + algebraMap R K W.a₁ * e x₀ = 0 := by
    have h : e (verticalDerivative W s b3 b4 b6) = 0 :=
      Ideal.algebraMap_residueField_eq_zero.mpr hd
    simpa only [verticalDerivative_eq, map_add, map_mul, map_ofNat, AlgHom.commutes,
      hz b3 h3, add_zero] using h
  have heq : e y₀ * (e y₀ + algebraMap R K W.a₁ * e x₀) = 0 := by
    have h := equation_map W s b3 b4 b6 e
    simp only [hz s hs, hz W.a₂ h2, hz b3 h3, hz b4 h4, hz b6 h6,
      zero_mul, add_zero] at h
    linear_combination h
  have hy : e y₀ = 0 := by
    rcases mul_eq_zero.mp heq with h | h
    · exact h
    · linear_combination hder - h
  have hx : e x₀ = 0 := by
    have ha' : algebraMap R K W.a₁ ≠ 0 := (ha.map (algebraMap R K)).ne_zero
    simpa only [hy, mul_zero, zero_add, mul_eq_zero, ha', false_or] using hder
  exact dividedCenter_not_smooth W s b3 b4 b6 p h3 h4 h6
    (Ideal.algebraMap_residueField_eq_zero.mp hx)
    (Ideal.algebraMap_residueField_eq_zero.mp hy) hp

end FLT.Mazur.WeierstrassDilatation

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantBranchCases
public import FLT.Mazur.WeierstrassDividedExactCoefficientDepth

/-!
# Secant branch classification at arbitrary pre-middle node depths

Every exact node depth strictly greater than twice the positive input
scale depth has the same three residue alternatives. The coefficient
vanishing is derived from the actual depth data, without a triple-depth
or divisibility-by-three hypothesis.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation IsLocalRing
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain R] [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n k : ℕ}
  (D : SplitNodeDepth W π n) (d : Data W π k)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "T" => DividedSecantRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "E" => dividedTangentDenominator W (π ^ k) d.b3 d.b4 d.b6 c a
local notation "C₂" => dividedTangentBranchFactor W (π ^ k) d.b3 d.b4 d.b6 c

include D

omit [IsDomain R] in
/-- Coefficients in the base maximal ideal vanish at every closed-fiber source prime. -/
theorem nodalSecant_coefficient_mem (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal) {z : R} (hz : z ∈ maximalIdeal R) :
    algebraMap R T z ∈ p.asIdeal := by
  rw [D.maximalIdeal_eq, Ideal.mem_span_singleton] at hz
  obtain ⟨b, hb⟩ := hz
  rw [hb, map_mul]
  exact p.asIdeal.mul_mem_right _ hp

/-- All pre-middle nodal secants lie in a strict branch or the smooth-output domain. -/
theorem nodalSecant_prime_three_cases (hk : 0 < k) (hdepth : 2 * k < n)
    (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal)
    (ha : ((j).comp a) (verticalDerivative W (π ^ k) d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hc : ((j).comp c) (verticalDerivative W (π ^ k) d.b3 d.b4 d.b6) ∉ p.asIdeal) :
    algebraMap S T (E * a (y W (π ^ k) d.b3 d.b4 d.b6)) ∉ p.asIdeal ∨
      algebraMap S T (E * C₂) ∉ p.asIdeal ∨
        dividedSecantX W (π ^ k) d.b3 d.b4 d.b6 a c ∉ p.asIdeal := by
  let K := p.asIdeal.ResidueField
  let e : T →ₐ[R] K := IsScalarTower.toAlgHom R T K
  have van (z : R) (hz : z ∈ maximalIdeal R) : algebraMap R K z = 0 := by
    rw [IsScalarTower.algebraMap_apply R T K]
    exact Ideal.algebraMap_residueField_eq_zero.mpr
      (nodalSecant_coefficient_mem D d a c p hp hz)
  have hπ : π ∈ maximalIdeal R := D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  have hs : algebraMap R K (π ^ k) = 0 := by rw [map_pow, van π hπ, zero_pow (Nat.ne_of_gt hk)]
  have hlin := divided_linear_deep_mem D d (show k ≤ n + 1 by omega)
  have h3 : d.b3 ∈ maximalIdeal R :=
    Ideal.pow_le_self (by omega) hlin.1
  have h4 : d.b4 ∈ maximalIdeal R :=
    Ideal.pow_le_self (by omega) hlin.2
  have h6 : d.b6 ∈ maximalIdeal R :=
    Ideal.pow_le_self (by omega) (divided_constant_exact_depth D d (by omega)).1
  have h := dividedSecant_residue_three_cases W (π ^ k) d.b3 d.b4 d.b6 a c e
    hs (van W.a₂ D.a₂_mem) (van d.b3 h3) (van d.b4 h4) (van d.b6 h6)
    ((D.a₁_unit.map (algebraMap R K)).ne_zero)
    (fun h => ha (Ideal.algebraMap_residueField_eq_zero.mp h))
    (fun h => hc (Ideal.algebraMap_residueField_eq_zero.mp h))
  simpa only [e, K, IsScalarTower.coe_toAlgHom', ne_eq,
    Ideal.algebraMap_residueField_eq_zero] using h

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantBranchCases
public import FLT.Mazur.WeierstrassDividedTripleDepthCoefficients

/-!
# Exact triple-depth secant primes lie in three explicit output domains

The nodal coefficient data imply every residue specialization needed by
the secant branch classification. Only the two actual input derivative
opens remain as source restrictions.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation IsLocalRing
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain R] [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (D : SplitNodeDepth W π (3 * k)) (d : Data W π k)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "T" => DividedSecantRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "E" => dividedTangentDenominator W (π ^ k) d.b3 d.b4 d.b6 c a
local notation "C₂" => dividedTangentBranchFactor W (π ^ k) d.b3 d.b4 d.b6 c

include D

omit [IsDomain R] in
/-- Coefficients in the base maximal ideal vanish at every closed-fiber source prime. -/
theorem tripleSecant_coefficient_mem (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal) {z : R} (hz : z ∈ maximalIdeal R) :
    algebraMap R T z ∈ p.asIdeal := by
  rw [D.maximalIdeal_eq, Ideal.mem_span_singleton] at hz
  obtain ⟨b, hb⟩ := hz
  rw [hb, map_mul]
  exact p.asIdeal.mul_mem_right _ hp

/-- Triple-depth secants with smooth vertical inputs lie in branches or smooth output. -/
theorem tripleSecant_prime_three_cases (p : PrimeSpectrum T)
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
      (tripleSecant_coefficient_mem D d a c p hp hz)
  have hk : k ≠ 0 := by have h := D.depth_pos; omega
  have hπ : π ∈ maximalIdeal R := D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  have hs : algebraMap R K (π ^ k) = 0 := by rw [map_pow, van π hπ, zero_pow hk]
  have h4 : algebraMap R K d.b4 = 0 := by
    have he := congrArg (algebraMap R K) (tripleDepthFourth_factor D d)
    simpa only [map_mul, hs, zero_mul] using he
  have h6 : algebraMap R K d.b6 = 0 := by
    have he := congrArg (algebraMap R K) (tripleDepthConstant_factor D d)
    simpa only [map_mul, hs, zero_mul] using he
  have h := dividedSecant_residue_three_cases W (π ^ k) d.b3 d.b4 d.b6 a c e
    hs (van W.a₂ D.a₂_mem) (van d.b3 (tripleDepth_third_mem D d)) h4 h6
    ((D.a₁_unit.map (algebraMap R K)).ne_zero)
    (fun h => ha (Ideal.algebraMap_residueField_eq_zero.mp h))
    (fun h => hc (Ideal.algebraMap_residueField_eq_zero.mp h))
  simpa only [e, K, IsScalarTower.coe_toAlgHom', ne_eq,
    Ideal.algebraMap_residueField_eq_zero] using h

end FLT.Mazur.WeierstrassDividedDepth

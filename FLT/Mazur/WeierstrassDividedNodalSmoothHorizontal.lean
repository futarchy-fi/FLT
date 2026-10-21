/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalInputSmoothVertical

/-!
# Smooth strict nodal inputs have nonzero horizontal coordinate

At a positive depth below the middle, a zero horizontal coordinate forces
the ordinate to vanish. The original relative smooth locus excludes that
center, so no puncture hypothesis is needed for a smooth nodal input.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {m k : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k)
local notation "A" => Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "base" => Spec.map (CommRingCat.ofHom (algebraMap R A))
local notation "x₀" => x W (π ^ k) d.b3 d.b4 d.b6
local notation "y₀" => y W (π ^ k) d.b3 d.b4 d.b6

include D in
/-- Smooth strict nodal divided points are horizontally punctured in the original chart. -/
theorem nodalDivided_smooth_horizontal (hk : 0 < k) (hm : 2 * k < m)
    (p : PrimeSpectrum A) (hp : algebraMap R A π ∈ p.asIdeal)
    (hs : p ∈ (base).smoothLocus) : x₀ ∉ p.asIdeal := by
  intro hx
  let K := p.asIdeal.ResidueField
  let ρ : A →ₐ[R] K := IsScalarTower.toAlgHom R A K
  have van (b : R) (hb : b ∈ maximalIdeal R) : algebraMap R K b = 0 := by
    rw [D.maximalIdeal_eq, Ideal.mem_span_singleton] at hb
    obtain ⟨v, hv⟩ := hb
    rw [IsScalarTower.algebraMap_apply R A K]
    apply Ideal.algebraMap_residueField_eq_zero.mpr
    rw [hv, map_mul]
    exact p.asIdeal.mul_mem_right _ hp
  have hlin := divided_linear_deep_mem D d (by omega : k ≤ m + 1)
  have h3 := van d.b3 (Ideal.pow_le_self (by omega) hlin.1)
  have h6 := van d.b6 (Ideal.pow_le_self (by omega)
    (divided_constant_exact_depth D d (by omega)).1)
  have hx0 : ρ x₀ = 0 := Ideal.algebraMap_residueField_eq_zero.mpr hx
  have he := equation_map W (π ^ k) d.b3 d.b4 d.b6 ρ
  simp only [hx0, h3, h6, zero_pow (by decide : 3 ≠ 0),
    zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero] at he
  have hy0 : ρ y₀ = 0 := (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp he
  have hd : ρ (verticalDerivative W (π ^ k) d.b3 d.b4 d.b6) = 0 := by
    simp only [verticalDerivative_eq, map_add, map_mul, map_ofNat, AlgHom.commutes,
      hy0, hx0, h3, mul_zero, add_zero]
  exact nodalDivided_smooth_vertical D d hk hm p hp hs
    (Ideal.algebraMap_residueField_eq_zero.mp hd)

variable {S : Type u} [CommRing S] [Algebra R S] (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)

include D in
/-- Any supplied smooth nodal input provides its own horizontal puncture. -/
theorem nodalDividedInput_smooth_horizontal (hk : 0 < k) (hm : 2 * k < m)
    (p : PrimeSpectrum S) (hp : algebraMap R S π ∈ p.asIdeal)
    (hs : Spec.map (CommRingCat.ofHom a.toRingHom) p ∈ (base).smoothLocus) :
    a x₀ ∉ p.asIdeal := by
  apply nodalDivided_smooth_horizontal D d hk hm (PrimeSpectrum.comap a.toRingHom p) _ hs
  change a (algebraMap R A π) ∈ p.asIdeal
  simpa only [AlgHom.commutes] using hp

end FLT.Mazur.WeierstrassDividedDepth

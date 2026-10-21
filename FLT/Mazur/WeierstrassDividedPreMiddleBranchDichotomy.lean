/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExactCoefficientDepth
public import FLT.Mazur.WeierstrassDividedTangentBranchSource

/-!
# Every positive pre-middle input lies on one of the two branches

The original coefficient depth conditions force the divided equation to
factor on the closed fiber. This supplies branch membership from the input
itself, without assuming a branch choice or smoothness of its contraction.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain R] [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {k m : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (hk : 0 < k) (hm : 2 * k < m) (p : PrimeSpectrum S)
  (hp : algebraMap R S π ∈ p.asIdeal)
local notation "x₁" => a (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "y₁" => a (y W (π ^ k) d.b3 d.b4 d.b6)

include D hm hp in
/-- Every divided third coefficient vanishes at a closed-fiber input in this range. -/
theorem preMiddleInput_b3_mem : algebraMap R S d.b3 ∈ p.asIdeal := by
  have hb := Ideal.pow_le_self (by omega : m + 1 - k ≠ 0)
    (divided_linear_deep_mem D d (by omega)).1
  rw [D.maximalIdeal_eq, Ideal.mem_span_singleton] at hb
  obtain ⟨v, hv⟩ := hb
  rw [hv, map_mul]
  exact p.asIdeal.mul_mem_right _ hp

include D hk hm hp in
/-- The original input equation forces one of the two complementary branch factors to vanish. -/
theorem preMiddleInput_branch_dichotomy :
    y₁ ∈ p.asIdeal ∨ dividedTangentBranchFactor W (π ^ k) d.b3 d.b4 d.b6 a ∈ p.asIdeal := by
  let F := p.asIdeal.ResidueField
  let ρ : S →ₐ[R] F := IsScalarTower.toAlgHom R S F
  have van (b : R) (hb : b ∈ maximalIdeal R) : algebraMap R F b = 0 := by
    rw [D.maximalIdeal_eq, Ideal.mem_span_singleton] at hb
    obtain ⟨v, hv⟩ := hb
    rw [IsScalarTower.algebraMap_apply R S F]
    apply Ideal.algebraMap_residueField_eq_zero.mpr
    rw [hv, map_mul]
    exact p.asIdeal.mul_mem_right _ hp
  have hπ0 : algebraMap R F π = 0 :=
    van π (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
  have hs : algebraMap R F (π ^ k) = 0 := by
    rw [map_pow, hπ0, zero_pow (by omega)]
  have h4 := van d.b4 (Ideal.pow_le_self (by omega)
    (divided_linear_deep_mem D d (by omega)).2)
  have h6 := van d.b6 (Ideal.pow_le_self (by omega)
    (divided_constant_exact_depth D d (by omega)).1)
  have he := equation_map W (π ^ k) d.b3 d.b4 d.b6 (ρ.comp a)
  simp only [AlgHom.comp_apply, hs, h4, h6, van W.a₂ D.a₂_mem,
    zero_mul, add_zero] at he
  have hz : ρ y₁ * ρ (dividedTangentBranchFactor W (π ^ k) d.b3 d.b4 d.b6 a) = 0 := by
    simp only [dividedTangentBranchFactor, map_add, map_mul, AlgHom.commutes]
    linear_combination he
  exact (mul_eq_zero.mp hz).imp Ideal.algebraMap_residueField_eq_zero.mp
    Ideal.algebraMap_residueField_eq_zero.mp

end FLT.Mazur.WeierstrassDividedDepth

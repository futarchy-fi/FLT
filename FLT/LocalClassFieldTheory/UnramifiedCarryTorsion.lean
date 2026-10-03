/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedCarryNormalization

/-!
# Torsion and finite-stage generation of integral unramified H2

The inflated degree-n carry is killed by exactly the integers divisible by n.
Every integral H2 class is an integer multiple of one of these finite-stage carries.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

attribute [local instance] trivialCoefficientAction trivialCoefficientIntComm
  trivialCoefficientContinuous rationalCircleCoefficientTopology rationalCircleCoefficientDiscrete

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]


local notation "U" => maximalUnramified R K C
local notation "Frob" => unramifiedFrobenius R K C

attribute [local instance] unramifiedH2Galois

/-- The exact annihilator of the degree-n carry is nZ. -/
theorem unramifiedCarryClass_zsmul_eq_zero (n : UnramifiedIndex) (j : ℤ) :
    j • unramifiedCarryClass R K C n = 0 ↔ (n.degree : ℤ) ∣ j := by
  rw [← unramifiedIntegralH2AddEquiv_eq_zero R K C,
    unramifiedCarryClass_zsmul_coordinate, ← zmodToRatCircle_intCast,
    zmodToRatCircle_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Multiplication by the finite-stage degree kills its carry class. -/
theorem unramifiedCarryClass_degree_smul (n : UnramifiedIndex) :
    (n.degree : ℤ) • unramifiedCarryClass R K C n = 0 :=
  (unramifiedCarryClass_zsmul_eq_zero R K C n _).mpr (dvd_refl _)

/-- Every integral unramified H2 class comes from a single finite cyclic stage. -/
theorem exists_unramifiedCarryClass_multiple (x : continuousCohomology ℤ Gal(U/K) ℤ 2) :
    ∃ (n : UnramifiedIndex) (j : ℤ), j • unramifiedCarryClass R K C n = x := by
  obtain ⟨q, hq⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℚ))
    (unramifiedIntegralH2AddEquiv R K C x)
  let n : UnramifiedIndex := ⟨⟨q.den, q.den_pos⟩⟩
  refine ⟨n, q.num, (unramifiedIntegralH2AddEquiv R K C).injective ?_⟩
  rw [unramifiedCarryClass_zsmul_coordinate]
  change (↑((q.num : ℚ) / q.den) : AddCircle (1 : ℚ)) = _
  rw [q.num_div_den]
  exact hq

/-- In particular every integral H2 class on the unramified quotient is torsion. -/
theorem unramifiedIntegralH2_torsion (x : continuousCohomology ℤ Gal(U/K) ℤ 2) :
    ∃ n : ℕ, 0 < n ∧ n • x = 0 := by
  obtain ⟨n, j, rfl⟩ := exists_unramifiedCarryClass_multiple R K C x
  refine ⟨n.degree, n.degree.pos, ?_⟩
  rw [smul_comm, ← natCast_zsmul, unramifiedCarryClass_degree_smul]
  exact zsmul_zero j

end LocalClassFieldTheory

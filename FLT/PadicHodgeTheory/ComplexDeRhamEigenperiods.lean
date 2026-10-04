/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexDeRhamFixedScalars

/-!
# Rank-one eigenperiods in the constructed de Rham field

Every cyclotomic eigenvector is a unique Q_p multiple of the corresponding
power of the existing logarithmic period. This uses the proved fixed-field
theorem and does not construct a crystalline period ring.
-/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Every integer power of the actual period is nonzero. -/
theorem complexCyclotomicFieldPeriod_zpow_ne_zero (n : ℤ) :
    complexCyclotomicFieldPeriod p ^ n ≠ 0 :=
  zpow_ne_zero n (complexCyclotomicLog_field_ne_zero p)

/-- Dividing by the actual period power removes its cyclotomic character. -/
theorem complexDeRham_eigenperiod_div_fixed (n : ℤ) (x : ComplexBDeRham p)
    (hx : ∀ σ : PadicGalois p, σ • x =
      complexPadicToDeRhamField p
        ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]) ^ n * x) :
    ∀ σ : PadicGalois p, σ • (x / complexCyclotomicFieldPeriod p ^ n) =
      x / complexCyclotomicFieldPeriod p ^ n := by
  intro σ
  let c := complexPadicToDeRhamField p
    ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]) ^ n
  have hs : σ • complexCyclotomicFieldPeriod p ^ n ≠ 0 := by
    exact (map_ne_zero_iff (MulSemiringAction.toRingEquiv (PadicGalois p)
      (ComplexBDeRham p) σ) (RingEquiv.injective _)).mpr
        (complexCyclotomicFieldPeriod_zpow_ne_zero p n)
  rw [complexCyclotomicFieldPeriod_zpow_smul] at hs
  have hc : c ≠ 0 := (mul_ne_zero_iff.mp hs).1
  change (MulSemiringAction.toRingEquiv (PadicGalois p) (ComplexBDeRham p) σ)
    (x / complexCyclotomicFieldPeriod p ^ n) = _
  rw [map_div₀]
  change (σ • x) / (σ • complexCyclotomicFieldPeriod p ^ n) = _
  rw [hx σ, complexCyclotomicFieldPeriod_zpow_smul]
  exact mul_div_mul_left _ _ hc

/-- The cyclotomic eigenspace consists precisely of unique scalar multiples of t^n. -/
theorem complexDeRham_eigenperiod_existsUnique (n : ℤ) (x : ComplexBDeRham p)
    (hx : ∀ σ : PadicGalois p, σ • x =
      complexPadicToDeRhamField p
        ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]) ^ n * x) :
    ∃! q : ℚ_[p], complexPadicToDeRhamField p q * complexCyclotomicFieldPeriod p ^ n = x := by
  obtain ⟨q, hq, hu⟩ := complexDeRham_fixed_existsUnique_scalar p
    (x / complexCyclotomicFieldPeriod p ^ n) (complexDeRham_eigenperiod_div_fixed p n x hx)
  refine ⟨q, (eq_div_iff (complexCyclotomicFieldPeriod_zpow_ne_zero p n)).mp hq, ?_⟩
  intro a ha
  exact hu a ((eq_div_iff (complexCyclotomicFieldPeriod_zpow_ne_zero p n)).mpr ha)

/-- Scalar multiples of t^n have the prescribed cyclotomic eigencharacter. -/
theorem complexDeRham_scalar_period_smul (n : ℤ) (q : ℚ_[p]) (σ : PadicGalois p) :
    σ • (complexPadicToDeRhamField p q * complexCyclotomicFieldPeriod p ^ n) =
      complexPadicToDeRhamField p
        ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]) ^ n *
          (complexPadicToDeRhamField p q * complexCyclotomicFieldPeriod p ^ n) := by
  rw [smul_mul', complexPadicToDeRhamField_fixed, complexCyclotomicFieldPeriod_zpow_smul]
  ring

end PadicHodgeTheory

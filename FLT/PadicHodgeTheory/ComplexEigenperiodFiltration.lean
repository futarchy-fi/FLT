/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexDeRhamEigenperiods
public import FLT.PadicHodgeTheory.ComplexIntegerGraded

/-!
# Exact filtration degree of cyclotomic eigenperiods

The existing integer filtration and logarithmic period give the exact jump:
a nonzero chi^n eigenperiod lies in Fil^n but not Fil^(n+1). In particular
the invariant coefficient for the covariant Tate twist has degree -1.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Scalar multiples of the actual t^n belong to the original nth filtration step. -/
theorem complexDeRham_scalar_period_mem (n : ℤ) (q : ℚ_[p]) :
    complexPadicToDeRhamField p q * complexCyclotomicFieldPeriod p ^ n ∈
      ComplexDeRhamIntegerFiltration p n := by
  exact Submodule.mem_span_singleton.mpr ⟨complexPadicToDeRham p q, by
    rw [Algebra.smul_def]; rfl⟩

/-- Such a scalar multiple belongs to the next step exactly when its scalar is zero. -/
theorem complexDeRham_scalar_period_mem_next_iff (n : ℤ) (q : ℚ_[p]) :
    complexPadicToDeRhamField p q * complexCyclotomicFieldPeriod p ^ n ∈
      ComplexDeRhamIntegerFiltration p (n + 1) ↔ q = 0 := by
  have h := congrArg (fun S : Submodule (ComplexBDeRhamPlus p) (ComplexBDeRhamPlus p) ↦
    complexPadicToDeRham p q ∈ S)
    (fractionalPrincipalNext_comap (K := ComplexBDeRham p)
      (complexCyclotomicLog_ne_zero p) n)
  change ((fractionalPrincipalEquiv (K := ComplexBDeRham p)
    (complexCyclotomicLog_ne_zero p) n (complexPadicToDeRham p q) : ComplexBDeRham p) ∈
      ComplexDeRhamIntegerFiltration p (n + 1)) =
        (complexPadicToDeRham p q ∈ Ideal.span {complexCyclotomicLog p}) at h
  rw [fractionalPrincipalEquiv_coe] at h
  change (_ ∈ ComplexDeRhamIntegerFiltration p (n + 1)) ↔ q = 0
  change (complexPadicToDeRhamField p q * complexCyclotomicFieldPeriod p ^ n ∈
    ComplexDeRhamIntegerFiltration p (n + 1)) = _ at h
  rw [h, complexCyclotomicLog_span, complexDeRham_maximalIdeal,
    ← complexDeRhamTheta_ker, RingHom.mem_ker,
    complexPadicToDeRham_theta]
  exact map_eq_zero_iff _ (algebraMap ℚ_[p] ℂ_[p]).injective

variable (n : ℤ) (x : ComplexBDeRham p)
  (hx : ∀ σ : PadicGalois p, σ • x =
    complexPadicToDeRhamField p
      ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]) ^ n * x)

include hx in
/-- Every eigenperiod lies in the filtration step prescribed by its character. -/
theorem complexDeRham_eigenperiod_mem : x ∈ ComplexDeRhamIntegerFiltration p n := by
  obtain ⟨q, rfl, _⟩ := complexDeRham_eigenperiod_existsUnique p n x hx
  exact complexDeRham_scalar_period_mem p n q

include hx in
/-- A nonzero eigenperiod has exactly the expected jump in the existing filtration. -/
theorem complexDeRham_eigenperiod_mem_next_iff :
    x ∈ ComplexDeRhamIntegerFiltration p (n + 1) ↔ x = 0 := by
  obtain ⟨q, rfl, _⟩ := complexDeRham_eigenperiod_existsUnique p n x hx
  rw [complexDeRham_scalar_period_mem_next_iff, mul_eq_zero]
  simp [complexCyclotomicFieldPeriod_zpow_ne_zero,
    map_eq_zero_iff _ (complexPadicToDeRhamField_injective p)]

end PadicHodgeTheory

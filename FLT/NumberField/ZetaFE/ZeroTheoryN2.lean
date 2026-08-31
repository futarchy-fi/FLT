/-
Copyright (c) 2026 Seed Fleet Fixture. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seed Fleet Fixture
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Exact modulus identities for the Gamma factor

This file proves node N2 from `cartography/odlyzko-m3-decomposition.md`.
-/

@[expose] public section

open Complex (Gamma I)
open Real
open Filter Topology
open scoped RealInnerProductSpace ComplexConjugate

namespace ZeroTheoryN2

/--
Node N2 from cartography/odlyzko-m3-decomposition.md:
Exact modulus identities for the Gamma factor.

For `t ≠ 0` we have:
- `‖Γ(1+it)‖² = π t / sinh (π t)`
- `‖Γ(1/2+it)‖² = π / cosh (π t)`

These are consequences of the reflection formula combined with
`Gamma_conj` and the functional equation.
-/
lemma Gamma_one_add_I_mul_sq_norm (t : ℝ) (ht : t ≠ 0) :
    ‖Gamma (1 + I * t)‖ ^ 2 = π * t / sinh (π * t) := by
  have hit : (I * (t : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast ht)
  have hsinh : Real.sinh (π * t) ≠ 0 := by
    rw [Real.sinh_ne_zero]
    exact mul_ne_zero Real.pi_ne_zero ht
  have hconj_arg : (starRingEnd ℂ) (1 + I * (t : ℂ)) = 1 - I * t := by
    apply Complex.ext <;> simp
  have hgamma_conj : Gamma (1 - I * t) = (starRingEnd ℂ) (Gamma (1 + I * t)) := by
    rw [← hconj_arg, Complex.Gamma_conj]
  have hrec : Gamma (1 - I * t) = -(I * t) * Gamma (-(I * t)) := by
    rw [show (1 - I * t : ℂ) = -(I * t) + 1 by ring]
    exact Complex.Gamma_add_one _ (neg_ne_zero.mpr hit)
  have hsin : Complex.sin (π * (1 + I * t)) = -(Real.sinh (π * t) : ℂ) * I := by
    rw [show (π : ℂ) * (1 + I * t) = (π : ℂ) + (π * t : ℝ) * I by push_cast; ring]
    rw [Complex.sin_add_mul_I]
    simp [Complex.ofReal_sinh]
  have href := Complex.Gamma_mul_Gamma_one_sub (1 + I * (t : ℂ))
  have href' : Gamma (1 + I * t) * Gamma (-(I * t)) =
      π / Complex.sin (π * (1 + I * t)) := by
    convert href using 1
    ring_nf
  have hprod : Gamma (1 + I * t) * (starRingEnd ℂ) (Gamma (1 + I * t)) =
      ((π * t / Real.sinh (π * t) : ℝ) : ℂ) := by
    rw [← hgamma_conj, hrec]
    rw [show Gamma (1 + I * t) * (-(I * t) * Gamma (-(I * t))) =
        -(I * t) * (Gamma (1 + I * t) * Gamma (-(I * t))) by ring]
    rw [href', hsin]
    field_simp [hsinh, Complex.I_ne_zero]
    norm_cast
    ring
  rw [Complex.mul_conj'] at hprod
  exact_mod_cast hprod

lemma Gamma_one_half_add_I_mul_sq_norm (t : ℝ) (ht : t ≠ 0) :
    ‖Gamma ((1 / 2 : ℂ) + I * t)‖ ^ 2 = π / cosh (π * t) := by
  have _ht := ht
  clear _ht ht
  have hconj_arg : (starRingEnd ℂ) ((1 / 2 : ℂ) + I * t) =
      (1 / 2 : ℂ) - I * t := by
    apply Complex.ext <;> norm_num
  have hone_sub : 1 - ((1 / 2 : ℂ) + I * t) = (1 / 2 : ℂ) - I * t := by ring
  have hgamma_conj : Gamma ((1 / 2 : ℂ) - I * t) =
      (starRingEnd ℂ) (Gamma ((1 / 2 : ℂ) + I * t)) := by
    rw [← hconj_arg, Complex.Gamma_conj]
  have hsin : Complex.sin (π * ((1 / 2 : ℂ) + I * t)) =
      (Real.cosh (π * t) : ℂ) := by
    rw [show (π : ℂ) * ((1 / 2 : ℂ) + I * t) =
        (π / 2 : ℂ) + (π * t : ℝ) * I by push_cast; ring]
    rw [Complex.sin_add_mul_I]
    simp [Complex.ofReal_cosh]
  have href := Complex.Gamma_mul_Gamma_one_sub ((1 / 2 : ℂ) + I * t)
  have hprod : Gamma ((1 / 2 : ℂ) + I * t) *
      (starRingEnd ℂ) (Gamma ((1 / 2 : ℂ) + I * t)) =
      ((π / Real.cosh (π * t) : ℝ) : ℂ) := by
    rw [← hgamma_conj, ← hone_sub, href, hsin]
    norm_cast
  rw [Complex.mul_conj'] at hprod
  exact_mod_cast hprod

end ZeroTheoryN2

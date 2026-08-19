/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Complex.Basic

/-!
# Gamma-factor modulus identities (Odlyzko node N2)

Exact modulus identities for the Gamma factor of the completed zeta function,
node N2 of `cartography/odlyzko-m3-decomposition.md`.

The two identities proved here are `‖Γ(1 + it)‖² = π t / sinh (π t)`, which
needs `t ≠ 0`, and `‖Γ(1/2 + it)‖² = π / cosh (π t)`, which holds for all real `t`.
-/

@[expose] public section

open Complex

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
    ‖Gamma (1 + I * t)‖ ^ 2 = Real.pi * t / Real.sinh (Real.pi * t) := by
  have hit : (I * (t : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast ht)
  have hsh : Real.sinh (Real.pi * t) ≠ 0 :=
    Real.sinh_ne_zero.2 (mul_ne_zero Real.pi_ne_zero ht)
  have hshc : ((Real.sinh (Real.pi * t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsh
  -- `sin (π · it) = sinh (πt) · i`
  have hsin : Complex.sin ((Real.pi : ℂ) * (I * t)) = ((Real.sinh (Real.pi * t) : ℝ) : ℂ) * I := by
    have h : ((Real.pi : ℝ) : ℂ) * (I * (t : ℂ)) = ((Real.pi * t : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [h, Complex.sin_mul_I, Complex.ofReal_sinh]
  -- reflection formula at `s = it`
  have hrefl : Gamma (I * t) * Gamma (1 - I * t)
      = ((Real.pi : ℝ) : ℂ) / (((Real.sinh (Real.pi * t) : ℝ) : ℂ) * I) := by
    rw [← hsin]; exact Complex.Gamma_mul_Gamma_one_sub _
  -- `Γ(1 + it) = it · Γ(it)`
  have hadd : Gamma (1 + I * t) = I * t * Gamma (I * t) := by
    rw [add_comm (1 : ℂ) (I * (t : ℂ))]
    exact Complex.Gamma_add_one _ hit
  have hconjarg : (starRingEnd ℂ) (1 + I * (t : ℂ)) = 1 - I * t := by
    simp [Complex.ext_iff]
  have hconj : Gamma (1 - I * t) = (starRingEnd ℂ) (Gamma (1 + I * t)) := by
    rw [← Complex.Gamma_conj, hconjarg]
  have hprod : Gamma (1 + I * t) * Gamma (1 - I * t)
      = ((Real.pi * t / Real.sinh (Real.pi * t) : ℝ) : ℂ) := by
    rw [hadd, mul_assoc, hrefl]
    push_cast
    field_simp
  have key : ((‖Gamma (1 + I * t)‖ : ℝ) : ℂ) ^ 2
      = ((Real.pi * t / Real.sinh (Real.pi * t) : ℝ) : ℂ) := by
    rw [← hprod, hconj, Complex.mul_conj']
  exact_mod_cast key

lemma Gamma_one_half_add_I_mul_sq_norm (t : ℝ) (_ht : t ≠ 0) :
    ‖Gamma ((1 / 2 : ℂ) + I * t)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
  have hch : ((Real.cosh (Real.pi * t) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.cosh_pos (Real.pi * t)).ne'
  -- `sin (π · (1/2 + it)) = cosh (πt)`
  have hsin : Complex.sin ((Real.pi : ℂ) * ((1 / 2 : ℂ) + I * t))
      = ((Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
    have h : ((Real.pi : ℝ) : ℂ) * ((1 / 2 : ℂ) + I * (t : ℂ))
        = ((Real.pi : ℝ) : ℂ) / 2 + ((Real.pi * t : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [h, Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two, one_mul, zero_mul,
      add_zero, Complex.cos_mul_I, Complex.ofReal_cosh]
  have hrefl : Gamma ((1 / 2 : ℂ) + I * t) * Gamma (1 - ((1 / 2 : ℂ) + I * t))
      = ((Real.pi : ℝ) : ℂ) / ((Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
    rw [← hsin]; exact Complex.Gamma_mul_Gamma_one_sub _
  have hone : (1 : ℂ) - ((1 / 2 : ℂ) + I * t) = (1 / 2 : ℂ) - I * t := by ring
  have hconjarg : (starRingEnd ℂ) ((1 / 2 : ℂ) + I * (t : ℂ)) = (1 / 2 : ℂ) - I * t := by
    simp [Complex.ext_iff]
  have hconj : Gamma ((1 / 2 : ℂ) - I * t) = (starRingEnd ℂ) (Gamma ((1 / 2 : ℂ) + I * t)) := by
    rw [← Complex.Gamma_conj, hconjarg]
  have key : ((‖Gamma ((1 / 2 : ℂ) + I * t)‖ : ℝ) : ℂ) ^ 2
      = ((Real.pi / Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
    push_cast
    rw [← Complex.mul_conj', ← hconj, ← hone, hrefl]
    push_cast
    ring
  exact_mod_cast key

end ZeroTheoryN2

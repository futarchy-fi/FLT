/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExactCoefficientDepth
public import FLT.Mazur.WeierstrassNodalDividedDepth

/-!
# Construct the shallow nodal output depth and its coefficient quotients

For 2k < m < 3k, the actual output depth is m - 2k, strictly between
zero and k. The divided constant at input depth has exactly this order;
its quotient is a unit. The fourth quotient still vanishes in the residue.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {m k : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k) (hdepth : 2 * k ≤ m)

include D hdepth in
/-- The actual fourth input coefficient is divisible by the smaller output scale. -/
theorem nodalLower_fourth_dvd : π ^ (m - 2 * k) ∣ d.b4 := by
  have h := (divided_linear_deep_mem D d (by omega)).2
  have h' : d.b4 ∈ maximalIdeal R ^ (m - 2 * k) :=
    Ideal.pow_le_pow_right (by omega) h
  rwa [D.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h'

include D hdepth in
/-- Exact constant depth provides the smaller-scale constant quotient. -/
theorem nodalLower_constant_dvd : π ^ (m - 2 * k) ∣ d.b6 := by
  have h := (divided_constant_exact_depth D d hdepth).1
  rwa [D.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h

/-- Construct the fourth quotient from the original nodal coefficients. -/
def nodalLowerFourth : R := (nodalLower_fourth_dvd D d hdepth).choose

/-- Construct the terminal constant quotient from its exact depth. -/
def nodalLowerConstant : R := (nodalLower_constant_dvd D d hdepth).choose

/-- The constructed fourth quotient retains the whole original input coefficient. -/
theorem nodalLowerFourth_factor :
    d.b4 = π ^ (m - 2 * k) * nodalLowerFourth D d hdepth :=
  (nodalLower_fourth_dvd D d hdepth).choose_spec

/-- The constructed constant quotient retains the whole original input coefficient. -/
theorem nodalLowerConstant_factor :
    d.b6 = π ^ (m - 2 * k) * nodalLowerConstant D d hdepth :=
  (nodalLower_constant_dvd D d hdepth).choose_spec

/-- The exact original node depth forces the terminal constant quotient to be invertible. -/
theorem nodalLowerConstant_isUnit : IsUnit (nodalLowerConstant D d hdepth) := by
  rw [← notMem_maximalIdeal]
  intro hb
  apply (divided_constant_exact_depth D d hdepth).2
  rw [nodalLowerConstant_factor D d hdepth]
  have hp : π ^ (m - 2 * k) ∈ maximalIdeal R ^ (m - 2 * k) :=
    Ideal.pow_mem_pow (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π) _
  simpa only [pow_succ] using Ideal.mul_mem_mul hp hb

/-- The fourth quotient still vanishes on the nodal fiber. -/
theorem nodalLowerFourth_mem : nodalLowerFourth D d hdepth ∈ maximalIdeal R := by
  have h := (divided_linear_deep_mem D d (by omega)).2
  have h' : d.b4 ∈ maximalIdeal R ^ ((m - 2 * k) + 1) :=
    Ideal.pow_le_pow_right (by omega) h
  have hc := nodalDepth_cancel D.uniformizer_ne_zero D.maximalIdeal_eq
    (m - 2 * k) 1 ((nodalLowerFourth_factor D d hdepth) ▸ h')
  simpa only [pow_one] using hc

omit [IsDomain R] in
/-- The original node conditions construct an actual datum at the lower output depth. -/
def nodalLowerData (hm : m ≤ 3 * k) : Data W π (m - 2 * k) :=
  (nodalDepth_exists_data D.maximalIdeal_eq (by omega : 2 * (m - 2 * k) ≤ m)
    D.a₃_mem D.a₄_mem D.a₆_mem).some

omit D d hdepth [IsDomain R] [IsLocalRing R] in
/-- The input scale factors through the lower output scale. -/
theorem nodalLower_scale_factor (hm : m ≤ 3 * k) :
    π ^ k = π ^ (m - 2 * k) * π ^ (k - (m - 2 * k)) := by
  rw [← pow_add, Nat.add_sub_of_le (by omega : m - 2 * k ≤ k)]

omit D d hdepth [IsDomain R] [IsLocalRing R] in
/-- Strictly below triple depth the unconsumed input scale vanishes on the nodal fiber. -/
theorem nodalLower_scale_zero (hm : m < 3 * k)
    {T : Type*} [CommRing T] (f : R →+* T) (hπ : f π = 0) :
    f (π ^ (k - (m - 2 * k))) = 0 := by
  rw [map_pow, hπ, zero_pow (by omega : k - (m - 2 * k) ≠ 0)]

end FLT.Mazur.WeierstrassDividedDepth

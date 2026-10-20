/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeSecondCoefficientNormalization
public import FLT.Mazur.WeierstrassDividedShearData

/-!
# Construct the second-coefficient factor for a finite branch depth

Choose the proved finite shear and its actual coefficient quotient. The
original node depth is preserved; no zero second coefficient or infinite
normalization is assumed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open IsLocalRing
variable {R : Type*} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {m : ℕ} (D : SplitNodeDepth W π m) (k : ℕ)

/-- The finite shear supplied by the second-coefficient normalization theorem. -/
def nodalSecondShear : R := (D.exists_second_coefficient_normalization k).choose

/-- The chosen shear is trivial on the original special fiber. -/
theorem nodalSecondShear_mem : nodalSecondShear D k ∈ maximalIdeal R :=
  (D.exists_second_coefficient_normalization k).choose_spec.1

/-- The original exact split-node depth survives the constructed shear. -/
theorem nodalSecondShear_depth :
    SplitNodeDepth (rootShearCurve W (nodalSecondShear D k)) π m :=
  (D.exists_second_coefficient_normalization k).choose_spec.2.1

/-- The actual sheared second coefficient is divisible by the requested scale. -/
theorem nodalSecondShear_dvd :
    π ^ k ∣ (rootShearCurve W (nodalSecondShear D k)).a₂ := by
  have h := (D.exists_second_coefficient_normalization k).choose_spec.2.2
  have h' : (rootShearCurve W (nodalSecondShear D k)).a₂ ∈ maximalIdeal R ^ k :=
    Ideal.pow_le_pow_right (Nat.le_succ k) h
  rwa [D.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h'

/-- The quotient needed in the actual strict-branch slope construction. -/
def nodalSecondQuotient : R := (nodalSecondShear_dvd D k).choose

/-- The constructed quotient gives the required exact coefficient factorization. -/
theorem nodalSecondQuotient_factor :
    (rootShearCurve W (nodalSecondShear D k)).a₂ = π ^ k * nodalSecondQuotient D k :=
  (nodalSecondShear_dvd D k).choose_spec

end FLT.Mazur.WeierstrassDividedDepth

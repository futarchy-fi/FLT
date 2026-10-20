/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalLowerCoefficients
public import FLT.Mazur.WeierstrassDividedNodalSecondNormalization

/-!
# Construct the normalization for the shallow output scale

The existing finite shear at input depth supplies a second coefficient
quotient at the smaller output depth. Its positive remaining scale proves
that this quotient vanishes on the nodal fiber; no normalization is assumed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {m k : ℕ} (D : SplitNodeDepth W π m)
local notation "V" => rootShearCurve W (nodalSecondShear D k)

/-- The chosen input-depth normalization induces the actual smaller-scale second quotient. -/
def nodalLowerSecondQuotient : R := π ^ (k - (m - 2 * k)) * nodalSecondQuotient D k

/-- The constructed smaller quotient factors the actual sheared second coefficient. -/
theorem nodalLowerSecondQuotient_factor (hm : m ≤ 3 * k) :
    (V).a₂ = π ^ (m - 2 * k) * nodalLowerSecondQuotient D (k := k) := by
  rw [nodalLowerSecondQuotient, nodalSecondQuotient_factor D k,
    nodalLower_scale_factor (π := π) hm, mul_assoc]

/-- Below triple node depth the smaller-scale second quotient has zero residue. -/
theorem nodalLowerSecondQuotient_mem (hm : m < 3 * k) :
    nodalLowerSecondQuotient D (k := k) ∈ IsLocalRing.maximalIdeal R := by
  have hp : π ∈ IsLocalRing.maximalIdeal R :=
    D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  have hw : π ^ (k - (m - 2 * k)) ∈ IsLocalRing.maximalIdeal R :=
    Ideal.pow_mem_of_mem _ hp _ (by omega)
  exact Ideal.mul_mem_right _ _ hw

end FLT.Mazur.WeierstrassDividedDepth

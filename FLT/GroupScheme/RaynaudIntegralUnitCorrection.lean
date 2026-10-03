/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.IntegralClosure

/-!
# Unit correction with integral extension coefficients

Coefficients may lie in an integral extension of the original base, including
an infinite strict henselization. Their units lift to units in the original
integral closure, so the original-base root-character construction still applies.
-/

@[expose] public noncomputable section
namespace RaynaudParameters

variable {O R L : Type*} [CommRing O] [CommRing R] [Field L] [Algebra O L]

/-- A homomorphism with integral values lifts to the integral closure of the original base. -/
def integralCoefficientMap (f : R →+* L) (hf : ∀ r, IsIntegral O (f r)) :
    R →+* IntegralClosure O L where
  toFun r := ⟨f r, hf r⟩
  map_zero' := Subtype.ext f.map_zero
  map_one' := Subtype.ext f.map_one
  map_add' a b := Subtype.ext (f.map_add a b)
  map_mul' a b := Subtype.ext (f.map_mul a b)

/-- A binary-weight root equation with integral extension units gives an original-base unit. -/
theorem exists_integral_unit_coordinate_ratio
    (f : R →+* L) (hf : ∀ r, IsIntegral O (f r))
    {π α x : L} {n m : ℕ} (hn : 0 < n) (hπ : π ≠ 0)
    (hα : α ^ n = π) (u : Rˣ) (hx : x ^ n = π ^ m * f u) :
    ∃ z : (IntegralClosure O L)ˣ, (z : IntegralClosure O L).val = x / α ^ m := by
  let ι := integralCoefficientMap f hf
  have hpow : (x / α ^ m) ^ n = f u := by
    rw [div_pow, pow_right_comm, hα, hx, mul_div_cancel_left₀]
    exact pow_ne_zero m hπ
  let z : IntegralClosure O L := ⟨x / α ^ m, IsIntegral.of_pow hn (by
    rw [hpow]
    exact hf u)⟩
  have hz : z ^ n = ι u := Subtype.ext hpow
  have hu : IsUnit z := (isUnit_pow_iff hn.ne').mp (by
    rw [hz]
    exact u.isUnit.map ι)
  exact ⟨hu.unit, congrArg Subtype.val hu.unit_spec⟩

end RaynaudParameters

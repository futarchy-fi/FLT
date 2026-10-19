/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluOrdinary
public import FLT.FreyCurve.Serre.VeluPointCofinite

/-!
# Detecting original function-field identities on geometric points

Nonzero functions have only finitely many zero abscissae. Thus equality on all
points above a cofinite set proves equality in the original quadratic field.
-/

@[expose] public section

namespace WeierstrassCurve.Velu

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  (E : WeierstrassCurve K) [E.IsElliptic]

/-- Cofinite equality on actual geometric points detects equality of rational functions. -/
theorem functionField_eq_of_cofinite {z w : FunctionField E}
    (h : ∀ᶠ x in Filter.cofinite, ∀ y, E.toAffine.Equation x y →
      affineValue E x y z = affineValue E x y w) : z = w := by
  by_contra hn
  have hz := eventually_affineValue_ne_zero E (sub_ne_zero.mpr hn)
  have hs := (EventuallyValue.self E z).sub E (EventuallyValue.self E w)
  obtain ⟨x, hx, hzx, hsx⟩ := (h.and (hz.and hs)).exists
  obtain ⟨y, hy⟩ := exists_nonsingular_ordinate E x
  apply hzx y hy.1
  exact (hsx y hy.1).trans (sub_eq_zero.mpr (hx y hy.1))

/-- Two expressions with the same eventual values are equal in the original field. -/
theorem EventuallyValue.unique {z w : FunctionField E} {f : K → K → K}
    (hz : EventuallyValue E z f) (hw : EventuallyValue E w f) : z = w := by
  apply functionField_eq_of_cofinite E
  filter_upwards [hz, hw] with x hx hw y hy
  exact (hx y hy).trans (hw y hy).symm

end WeierstrassCurve.Velu

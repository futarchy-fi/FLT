/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.NTorsionRoots

/-!
# A chart containing odd torsion

The linear form `2Y + a₁X + a₃Z` vanishes precisely at affine two-torsion.
Consequently odd torsion lies in its complement, including the identity when
2 is invertible. The polynomial separation holds over every coefficient ring
with unit discriminant, including residue fields at the torsion prime.
-/

@[expose] public section

open Polynomial
namespace WeierstrassCurve

/-- Odd division polynomials and the two-division polynomial are coprime over
any ring with unit discriminant, even when the odd index is not a unit. -/
theorem isCoprime_preΨ_ΨSq_two_of_isUnit {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ) {n : ℕ} (hn : Odd n) :
    IsCoprime (W.preΨ n) (W.ΨSq 2) := by
  let : W.IsElliptic := ⟨hΔ⟩
  rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq,
    ← Ideal.span_union, Set.singleton_union]
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
  let : M.IsMaximal := hM
  let : Field (R[X] ⧸ M) := Ideal.Quotient.field M
  let f : R →+* R[X] ⧸ M := (Ideal.Quotient.mk M).comp C
  have hc := (W.map f).isCoprime_preΨ_ΨSq_two hn
  have he (p : R[X]) : (p.map f).eval (Ideal.Quotient.mk M X) = Ideal.Quotient.mk M p := by
    rw [eval_map, show f = (Ideal.Quotient.mk M).comp C from rfl,
      ← hom_eval₂, eval₂_C_X]
  have hψ : Ideal.Quotient.mk M (W.preΨ n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (by simp)))
  have hψ₂ : Ideal.Quotient.mk M (W.ΨSq 2) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (by simp)))
  have hh := hc.map (Polynomial.evalRingHom (Ideal.Quotient.mk M X))
  simp only [map_preΨ, map_ΨSq, coe_evalRingHom, he, hψ, hψ₂] at hh
  exact not_isCoprime_zero_zero hh

variable {k : Type*} [Field k] (E : WeierstrassCurve k) [DecidableEq k]

/-- A nonzero odd-torsion point avoids the line fixed by negation. -/
theorem two_mul_y_add_ne_zero_of_odd_torsion {x y : k}
    (h : E.toAffine.Nonsingular x y) {n : ℕ} (hn : Odd n)
    (ht : n • Affine.Point.some x y h = 0) :
    2 * y + E.a₁ * x + E.a₃ ≠ 0 := by
  intro hz
  have hy : y = E.toAffine.negY x y := by
    simp only [Affine.negY]
    linear_combination hz
  have htwo : 2 • Affine.Point.some x y h = 0 := by
    rw [two_nsmul]
    exact Affine.Point.add_self_of_Y_eq hy
  obtain ⟨m, rfl⟩ := hn
  rw [add_nsmul, mul_nsmul, htwo, smul_zero, one_nsmul, zero_add] at ht
  exact Affine.Point.some_ne_zero h ht

end WeierstrassCurve

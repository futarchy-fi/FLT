/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.VeluPadicTwoComponents
public import FLT.Mazur.RationalPadicIntegralDepth

/-!
# Rational invariant valuations of the actual target at two

The canonical integral equation computes the valuations of the original
rational invariants. Its c₄ has valuation zero. Under an injective rational
p-torsion map, Δ has positive p-divisible valuation and j has negative
p-divisible valuation. This is local arithmetic, not cusp orientation.
-/

@[expose] public section

namespace FreyPackage

open WeierstrassCurve FLT.Mazur
open scoped WeierstrassCurve.Affine

variable {P : FreyPackage} {E : WeierstrassCurve ℚ}

/-- The original rational c₄ is nonzero and is a two-adic unit. -/
theorem IsVeluTarget.two_c4_valuation (h : P.IsVeluTarget E) :
    E.c₄ ≠ 0 ∧ padicValRat 2 E.c₄ = 0 := by
  obtain ⟨W, hw, hc⟩ := h.exists_padic_two_unit_model
  have he := congrArg WeierstrassCurve.c₄ hw
  rw [map_c₄, map_c₄] at he
  refine ⟨?_, rationalPadicIntegral_unit_valuation 2 E.c₄ W.c₄ he hc⟩
  intro hz
  apply (hc.map (algebraMap (padicIntegerSubring 2) ℚ_[2])).ne_zero
  rw [he, hz, map_zero]

/-- The actual rational target discriminant has positive valuation divisible by p at two. -/
theorem IsVeluTarget.two_discriminant_valuation (h : P.IsVeluTarget E)
    (hp17 : 17 ≤ P.p) (f : ZMod P.p →+ (E⁄ℚ).Point) (hf : Function.Injective f) :
    0 < padicValRat 2 E.Δ ∧ (P.p : ℤ) ∣ padicValRat 2 E.Δ := by
  classical
  let _ := h.isElliptic
  obtain ⟨W, _, hw, _, _, _, _, _, n, hn, hd, hd', hpn⟩ :=
    h.exists_canonical_two_component_model hp17 f hf
  have he := congrArg WeierstrassCurve.Δ hw
  rw [map_Δ, map_Δ] at he
  rw [rationalPadicIntegral_depth 2 E.Δ W.Δ he n hd hd']
  exact ⟨by exact_mod_cast hn, by exact_mod_cast hpn⟩

/-- Unit c₄ makes the actual j valuation the negative discriminant valuation. -/
theorem IsVeluTarget.two_j_valuation_eq (h : P.IsVeluTarget E) :
    let _ := h.isElliptic
    padicValRat 2 E.j = -padicValRat 2 E.Δ := by
  dsimp only
  let _ := h.isElliptic
  obtain ⟨hc, hv⟩ := h.two_c4_valuation
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, coe_Δ',
    padicValRat.mul (inv_ne_zero E.isUnit_Δ.ne_zero) (pow_ne_zero 3 hc),
    padicValRat.inv, padicValRat.pow, hv, mul_zero, add_zero]

/-- The actual target has negative p-divisible j valuation at two when it carries p-torsion. -/
theorem IsVeluTarget.two_j_valuation (h : P.IsVeluTarget E)
    (hp17 : 17 ≤ P.p) (f : ZMod P.p →+ (E⁄ℚ).Point) (hf : Function.Injective f) :
    let _ := h.isElliptic
    padicValRat 2 E.j < 0 ∧ (P.p : ℤ) ∣ padicValRat 2 E.j := by
  dsimp only
  let _ := h.isElliptic
  obtain ⟨hpos, hd⟩ := h.two_discriminant_valuation hp17 f hf
  rw [h.two_j_valuation_eq]
  exact ⟨neg_neg_of_pos hpos, dvd_neg.mpr hd⟩

end FreyPackage

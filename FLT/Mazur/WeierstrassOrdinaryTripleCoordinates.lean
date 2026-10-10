/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassTripleCenteredRelations

/-!
# Associativity coordinates for ordinary inner laws and secant outer laws

The four actual line equations and the two inner divided differences force
both iterated outputs to agree. The hypotheses allow either ordinary inner
chart and only require the denominators of the two outer secant charts.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralAddition

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve.Affine R)

/-- Ordinary inner sums and secant outer sums give the same two affine coordinates. -/
theorem ordinary_triple_add_coordinates {x₁ x₂ x₃ y₁ y₂ y₃ l m n o : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂)
    (hm : m * (x₂ - x₃) = y₂ - y₃)
    (hcl : l * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁)
    (hcm : m * (y₂ + y₃ + W.a₁ * x₃ + W.a₃) =
      x₂ ^ 2 + x₂ * x₃ + x₃ ^ 2 + W.a₂ * (x₂ + x₃) + W.a₄ - W.a₁ * y₂)
    (hn : n * (W.addX x₁ x₂ l - x₃) = W.addY x₁ x₂ y₁ l - y₃)
    (ho : o * (x₁ - W.addX x₂ x₃ m) = y₁ - W.addY x₂ x₃ y₂ m)
    (hd : IsUnit (W.addX x₁ x₂ l - x₃))
    (he : IsUnit (x₁ - W.addX x₂ x₃ m)) :
    W.addX (W.addX x₁ x₂ l) x₃ n = W.addX x₁ (W.addX x₂ x₃ m) o ∧
      W.addY (W.addX x₁ x₂ l) x₃ (W.addY x₁ x₂ y₁ l) n =
        W.addY x₁ (W.addX x₂ x₃ m) y₁ o := by
  have hu : W.addX x₁ x₂ l - x₂ =
      l ^ 2 + W.a₁ * l - (W.a₂ + 3 * x₂) - (x₁ - x₂) := by
    simp only [Affine.addX]
    ring
  have hv : W.addX x₂ x₃ m - x₂ =
      m ^ 2 + W.a₁ * m - (W.a₂ + 3 * x₂) - (x₃ - x₂) := by
    simp only [Affine.addX]
    ring
  have hd' : IsUnit ((W.addX x₁ x₂ l - x₂) - (x₃ - x₂)) := by
    convert hd using 1
    ring
  have he' : IsUnit ((x₁ - x₂) - (W.addX x₂ x₃ m - x₂)) := by
    convert he using 1
    ring
  have hnc := triple_left_line_centered W hl hm hn
  obtain ⟨hs, ht⟩ := triple_slope_identities hu hv
    (triple_inner_cross W hl hm hcl hcm) hnc
    (triple_right_line_centered W hl ho) hd' he'
  have hL : W.addX (W.addX x₁ x₂ l) x₃ n - x₂ =
      (n + l + W.a₁) * (n - m) := by
    convert triple_left_abscissa hu ht using 1
    simp only [Affine.addX]
    ring
  have hR : W.addX x₁ (W.addX x₂ x₃ m) o - x₂ =
      (n + l + W.a₁) * (n - m) := by
    convert triple_right_abscissa hv hs ht using 1
    simp only [Affine.addX]
    ring
  constructor
  · exact sub_left_inj.mp (hL.trans hR.symm)
  · apply (sub_left_inj (a := y₂)).mp
    rw [triple_left_ordinate_centered W hl, triple_right_ordinate_centered W hl, hL, hR]
    exact triple_ordinate rfl hs ht hnc

end FLT.Mazur.WeierstrassIntegralAddition

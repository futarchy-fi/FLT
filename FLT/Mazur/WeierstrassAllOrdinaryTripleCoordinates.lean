/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassTripleCenteredCubics

/-!
# Associativity coordinates for all ordinary addition charts

Both inner charts and both outer charts may independently be secant or tangent.
The original line and divided-difference relations, together with each chosen
outer denominator unit, imply equality of the two actual affine outputs.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralAddition

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve.Affine R)

/-- Every combination of four ordinary charts gives the same two affine coordinates. -/
theorem all_ordinary_triple_add_coordinates {x₁ x₂ x₃ y₁ y₂ y₃ l m n o : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂)
    (hm : m * (x₂ - x₃) = y₂ - y₃)
    (hcl : l * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁)
    (hcm : m * (y₂ + y₃ + W.a₁ * x₃ + W.a₃) =
      x₂ ^ 2 + x₂ * x₃ + x₃ ^ 2 + W.a₂ * (x₂ + x₃) + W.a₄ - W.a₁ * y₂)
    (hn : n * (W.addX x₁ x₂ l - x₃) = W.addY x₁ x₂ y₁ l - y₃)
    (ho : o * (x₁ - W.addX x₂ x₃ m) = y₁ - W.addY x₂ x₃ y₂ m)
    (hcn : n * (W.addY x₁ x₂ y₁ l + y₃ + W.a₁ * x₃ + W.a₃) =
      (W.addX x₁ x₂ l) ^ 2 + W.addX x₁ x₂ l * x₃ + x₃ ^ 2 +
        W.a₂ * (W.addX x₁ x₂ l + x₃) + W.a₄ - W.a₁ * W.addY x₁ x₂ y₁ l)
    (hco : o * (y₁ + W.addY x₂ x₃ y₂ m + W.a₁ * W.addX x₂ x₃ m + W.a₃) =
      x₁ ^ 2 + x₁ * W.addX x₂ x₃ m + (W.addX x₂ x₃ m) ^ 2 +
        W.a₂ * (x₁ + W.addX x₂ x₃ m) + W.a₄ - W.a₁ * y₁)
    (hd : IsUnit (W.addX x₁ x₂ l - x₃) ∨
      IsUnit (W.addY x₁ x₂ y₁ l + y₃ + W.a₁ * x₃ + W.a₃))
    (he : IsUnit (x₁ - W.addX x₂ x₃ m) ∨
      IsUnit (y₁ + W.addY x₂ x₃ y₂ m + W.a₁ * W.addX x₂ x₃ m + W.a₃)) :
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
  have hd' : IsUnit ((W.addX x₁ x₂ l - x₂) - (x₃ - x₂)) ∨
      IsUnit (-(l + W.a₁) * (W.addX x₁ x₂ l - x₂) + (m + W.a₁) * (x₃ - x₂)) := by
    rcases hd with hd | hd
    · left
      convert hd using 1
      ring
    · right
      convert hd using 1
      simp only [Affine.addY, Affine.negY, Affine.negAddY]
      linear_combination -hl - hm
  have he' : IsUnit ((x₁ - x₂) - (W.addX x₂ x₃ m - x₂)) ∨
      IsUnit (l * (x₁ - x₂) - m * (W.addX x₂ x₃ m - x₂)) := by
    rcases he with he | he
    · left
      convert he using 1
      ring
    · right
      convert he using 1
      simp only [Affine.addY, Affine.negY, Affine.negAddY]
      linear_combination hl
  have hnc := triple_left_line_centered W hl hm hn
  have hzv := triple_last_product W hm hcm
  have ht := triple_left_parameter hu hv (triple_first_product W hl hcl) hzv hnc
    (triple_left_cubic_centered W hl hm hcn) hd'
  have hs := triple_outer_slopes hu hv hzv hnc (triple_right_line_centered W hl ho)
    (triple_right_cubic_centered W hl hco) ht he'
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

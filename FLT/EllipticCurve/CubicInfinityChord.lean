/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicProjectiveAddition

/-! # A chord law regular near infinity plus infinity

In the Y=1 chart the divided difference in Z is a unit at infinity.
It supplies the tangent direction without dividing by the difference of
the input X-coordinates. The resulting homogeneous sum is nonzero at (O,O). -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Divided difference in the Z coordinate of the infinity-chart equation. -/
def infinityChordDenominator (r v w : R) : R :=
  1 + W.a₁ * r + W.a₃ * (w + v) - W.a₂ * r ^ 2 -
    W.a₄ * r * (w + v) - W.a₆ * (w ^ 2 + w * v + v ^ 2)

/-- Negative divided difference in the X coordinate of the infinity-chart equation. -/
def infinityChordNumerator (u r v : R) : R :=
  r ^ 2 + r * u + u ^ 2 + W.a₂ * (r + u) * v + W.a₄ * v ^ 2 - W.a₁ * v

theorem infinity_chord_relation {u v r w : R}
    (hP : W.toProjective.Equation ![u, 1, v])
    (hQ : W.toProjective.Equation ![r, 1, w]) :
    (w - v) * infinityChordDenominator W r v w =
      (r - u) * infinityChordNumerator W u r v := by
  rw [Projective.equation_iff] at hP hQ
  simp only [Projective.fin3_def_ext] at hP hQ
  unfold infinityChordDenominator infinityChordNumerator
  linear_combination hQ - hP

/-- Linear coefficient of the infinity-chart cubic on a line with direction (1,l). -/
def infinityLineLinear (u v l : R) : R :=
  W.a₁ * l * u + W.a₁ * v - W.a₂ * l * u ^ 2 - 2 * W.a₂ * u * v +
    2 * W.a₃ * l * v - 2 * W.a₄ * l * u * v - W.a₄ * v ^ 2 -
    3 * W.a₆ * l * v ^ 2 + l - 3 * u ^ 2

/-- Quadratic coefficient of the infinity-chart cubic on the line. -/
def infinityLineQuadratic (u v l : R) : R :=
  W.a₁ * l - 2 * W.a₂ * l * u - W.a₂ * v + W.a₃ * l ^ 2 -
    W.a₄ * l ^ 2 * u - 2 * W.a₄ * l * v - 3 * W.a₆ * l ^ 2 * v - 3 * u

/-- Cubic coefficient of the infinity-chart cubic on the line. -/
def infinityLineCubic (l : R) : R := -W.a₂ * l - W.a₄ * l ^ 2 - W.a₆ * l ^ 3 - 1

theorem infinity_line_expansion (u v l s t : R) :
    cubicForm W ![s * u + t, s, s * v + l * t] =
      s ^ 3 * cubicForm W ![u, 1, v] + s ^ 2 * t * infinityLineLinear W u v l +
        s * t ^ 2 * infinityLineQuadratic W u v l + t ^ 3 * infinityLineCubic W l := by
  dsimp [cubicForm, infinityLineLinear, infinityLineQuadratic, infinityLineCubic]
  ring

theorem infinity_line_residual {u v r w l : R}
    (hl : w - v = l * (r - u))
    (hn : l * infinityChordDenominator W r v w = infinityChordNumerator W u r v) :
    infinityLineLinear W u v l + infinityLineQuadratic W u v l * (r - u) +
      infinityLineCubic W l * (r - u) ^ 2 = 0 := by
  unfold infinityChordDenominator infinityChordNumerator at hn
  unfold infinityLineLinear infinityLineQuadratic infinityLineCubic
  linear_combination hn +
    (-W.a₃ * l + W.a₄ * l * r + W.a₆ * l ^ 2 * r - W.a₆ * l ^ 2 * u +
      2 * W.a₆ * l * v + W.a₆ * l * w) * hl

/-- Homogeneous parameter for the remaining intersection with the line. -/
def infinityChordParameter (u v r l : R) : R :=
  -infinityLineQuadratic W u v l - infinityLineCubic W l * (r - u)

/-- Homogeneous sum obtained from the residual intersection in the infinity chart. -/
def infinityChord (u v r l : R) : Fin 3 → R :=
  let c := infinityLineCubic W l
  let t := infinityChordParameter W u v r l
  W.toProjective.neg ![c * u + t, c, c * v + l * t]

theorem infinityChord_equation {u v r w l : R}
    (hP : W.toProjective.Equation ![u, 1, v])
    (hl : w - v = l * (r - u))
    (hn : l * infinityChordDenominator W r v w = infinityChordNumerator W u r v) :
    W.toProjective.Equation (infinityChord W u v r l) := by
  apply projective_neg_equation
  rw [equation_iff_cubicForm]
  rw [infinity_line_expansion, (equation_iff_cubicForm W _).mp hP]
  have hr := infinity_line_residual W hl hn
  unfold infinityChordParameter
  linear_combination infinityLineCubic W l ^ 2 *
    (-infinityLineQuadratic W u v l - infinityLineCubic W l * (r - u)) * hr

@[simp] theorem infinityChord_origin :
    infinityChord W 0 0 0 0 = ![0, 1, 0] := by
  ext i
  fin_cases i <;>
    simp [infinityChord, infinityChordParameter, infinityLineQuadratic,
      infinityLineCubic, Projective.neg, Projective.negY, Projective.fin3_def_ext]

theorem infinityChord_baseChange {A B : Type*} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (u v r l : A) :
    f ∘ infinityChord (W.map (algebraMap R A)) u v r l =
      infinityChord (W.map (algebraMap R B)) (f u) (f v) (f r) (f l) := by
  ext i
  fin_cases i <;>
    simp [infinityChord, infinityChordParameter, infinityLineCubic, infinityLineQuadratic,
      Projective.neg, Projective.negY, WeierstrassCurve.map, map_ofNat]

theorem infinityChordNumerator_baseChange {A B : Type*} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (u r v : A) :
    f (infinityChordNumerator (W.map (algebraMap R A)) u r v) =
      infinityChordNumerator (W.map (algebraMap R B)) (f u) (f r) (f v) := by
  simp [infinityChordNumerator, WeierstrassCurve.map]

end WeierstrassCurve.CubicCharts

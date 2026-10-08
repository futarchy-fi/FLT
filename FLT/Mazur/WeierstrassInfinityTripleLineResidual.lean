/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityLineReconstruction
public import FLT.Mazur.WeierstrassInfinityTripleOuterDifference
public import FLT.Mazur.WeierstrassInfinityTripleComparison

/-!
# An exact line-residual criterion for infinity associativity

The actual output-line relation reconstructs both normalized coordinate
differences from one line residual and one homogeneous minor. Thus their
vanishing is an exact criterion, even when negated Y coordinates are not units.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The homogeneous Y coordinate of the negation of an actual normalized point. -/
def infinityTripleNegY (i : Fin 7) : Γ(InfinityTripleFull W hΔ, ⊤) :=
  let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
  (-1 - A.a₁ * infinityTripleScalarX W hΔ i - A.a₃ * infinityTripleScalarZ W hΔ i)

/-- The residual of the negated point `i` on the actual input line `j`. -/
def infinityTripleNegLineResidual (i : Fin 7) (j : Fin 4) :
    Γ(InfinityTripleFull W hΔ, ⊤) :=
  infinityTripleScalarZ W hΔ i -
    infinityTripleScalarSlope W hΔ j * infinityTripleScalarX W hΔ i -
    infinityTripleLineIntercept W hΔ j * infinityTripleNegY W hΔ i

/-- The XY minor of the negations of two actual normalized points. -/
def infinityTripleNegMinor (i k : Fin 7) : Γ(InfinityTripleFull W hΔ, ⊤) :=
  infinityTripleNegY W hΔ i * infinityTripleScalarX W hΔ k -
    infinityTripleScalarX W hΔ i * infinityTripleNegY W hΔ k

/-- Each actual output has zero residual on its own input line after negation. -/
theorem infinityTripleNegLineResidual_output (j : Fin 4) :
    infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex j) j = 0 := by
  unfold infinityTripleNegLineResidual infinityTripleNegY infinityTripleLineIntercept
  linear_combination infinityTripleScalar_output_line W hΔ j

/-- Both actual normalized coordinatedifferences are reconstructed from two residuals. -/
theorem infinityTripleScalar_difference_residual (i : Fin 7) (j : Fin 4) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let k := infinityTripleOutputIndex j
    let b := infinityTripleLineIntercept W hΔ j
    let m := infinityTripleScalarSlope W hΔ j
    infinityTripleScalarX W hΔ i - infinityTripleScalarX W hΔ k =
        -(1 + A.a₃ * b) * infinityTripleNegMinor W hΔ k i +
          A.a₃ * infinityTripleScalarX W hΔ k * infinityTripleNegLineResidual W hΔ i j ∧
      infinityTripleScalarZ W hΔ i - infinityTripleScalarZ W hΔ k =
        (A.a₁ * b - m) * infinityTripleNegMinor W hΔ k i +
          (1 + A.a₃ * infinityTripleScalarZ W hΔ k) *
            infinityTripleNegLineResidual W hΔ i j := by
  exact ⟨infinity_negated_line_difference_x _
    (infinityTripleNegLineResidual_output W hΔ j) _ _,
    infinity_negated_line_difference_z _ (infinityTripleNegLineResidual_output W hΔ j) _ _⟩

/-- Comparing any actual point with an output reduces exactly to a residual and a minor. -/
theorem infinityTripleScalar_eq_iff_residual (i : Fin 7) (j : Fin 4) :
    (infinityTripleScalarX W hΔ i =
        infinityTripleScalarX W hΔ (infinityTripleOutputIndex j) ∧
      infinityTripleScalarZ W hΔ i =
        infinityTripleScalarZ W hΔ (infinityTripleOutputIndex j)) ↔
      infinityTripleNegLineResidual W hΔ i j = 0 ∧
        infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j) i = 0 :=
  infinity_negated_line_eq_iff _ (infinityTripleNegLineResidual_output W hΔ j)

/-- On the true member, associativity is exactly two explicitly constructed residuals. -/
theorem infinityTripleFull_assoc_iff_line_residual :
    infinityTripleFullMap W hΔ ≫ integralCurveTripleAddLeft W hΔ =
        infinityTripleFullMap W hΔ ≫ integralCurveTripleAddRight W hΔ ↔
      infinityTripleNegLineResidual W hΔ 6 2 = 0 ∧
        infinityTripleNegMinor W hΔ 5 6 = 0 := by
  rw [infinityTripleFull_assoc_iff_coordinates, eq_comm (a := infinityTripleScalarX W hΔ 5),
    eq_comm (a := infinityTripleScalarZ W hΔ 5)]
  exact infinityTripleScalar_eq_iff_residual W hΔ 6 2

end FLT.Mazur.WeierstrassIntegralChart
